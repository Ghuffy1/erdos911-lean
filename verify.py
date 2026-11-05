"""Rebuild and audit the exact Erdős 911 proof (Python standard library only)."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_order() -> list[Path]:
    sources = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p
               for p in (ROOT / "Erdos911").rglob("*.lean")}
    sources["Erdos911"] = ROOT / "Erdos911.lean"
    ordered, visiting, done = [], set(), set()

    def visit(name: str) -> None:
        if name in done:
            return
        if name in visiting:
            raise RuntimeError(f"Cyclic imports at {name}")
        visiting.add(name)
        for dep in re.findall(r"^import\s+(Erdos911(?:\.[A-Za-z0-9_]+)*)", sources[name].read_text(encoding="utf-8-sig"), re.M):
            if dep not in sources:
                raise RuntimeError(f"Missing project import {dep}")
            visit(dep)
        visiting.remove(name)
        done.add(name)
        ordered.append(sources[name])

    for name in sorted(sources):
        visit(name)
    return ordered


def run_checked(command: list[str], log: Path, env: dict[str, str], *, allow_warnings: bool = False) -> None:
    with log.open("w", encoding="utf-8") as out:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    text = log.read_text(encoding="utf-8-sig")
    if result.returncode or re.search(r"\berror(?:\(|:)|sorryAx", text):
        raise RuntimeError(f"Verification failed ({result.returncode}): {log}\n{text[-12000:]}")
    if not allow_warnings and re.search(r"\bwarning:", text):
        raise RuntimeError(f"Compiler warning requires review: {log}\n{text[-8000:]}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-cache", type=Path, default=ROOT / ".lake/packages")
    parser.add_argument("--build-dir", type=Path, default=ROOT / ".lake/verification/lib/lean")
    parser.add_argument("--report-dir", type=Path, default=ROOT / "audit/clean-full")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--resume", action="store_true", help="Resume only a hash-verified prefix of this isolated build.")
    args = parser.parse_args()
    build, logs, cache = args.build_dir.resolve(), args.report_dir.resolve(), args.package_cache.resolve()
    if not build.is_relative_to(ROOT / ".lake"):
        raise RuntimeError("The isolated build directory must be within this project's .lake directory.")
    if build.exists() and any(build.rglob("*.olean")) and not args.resume:
        raise RuntimeError("Choose an empty build directory; this verifier never reuses project oleans.")
    if not cache.is_dir():
        raise RuntimeError(f"Missing dependency cache: {cache}")
    build.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    sources = module_order()
    before = {p.relative_to(ROOT).as_posix(): sha(p) for p in sources}
    progress_path = logs / "progress.json"
    if args.resume:
        state = json.loads(progress_path.read_text(encoding="utf-8-sig"))
    else:
        state = {"initial_started_at_utc": datetime.now(timezone.utc).isoformat(),
                 "initial_source_sha256": before, "completed": [], "prior_attempts": []}
    resume_count = len(state["completed"])
    if resume_count:
        for source, record in zip(sources, state["completed"], strict=False):
            relative = source.relative_to(ROOT)
            output = (build / relative).with_suffix(".olean")
            log = logs / record["log"]
            assert record["source"] == relative.as_posix()
            assert sha(source) == record["source_sha256"], f"Changed source in completed prefix: {relative}"
            assert sha(output) == record["output_sha256"], f"Changed output in completed prefix: {relative}"
            assert sha(log) == record["log_sha256"], f"Changed log in completed prefix: {relative}"
        assert resume_count <= len(sources)
        print(f"Verified unchanged source/output/log hashes for {resume_count} completed modules.", flush=True)
    state.setdefault("resume_points", []).append({"at_utc": datetime.now(timezone.utc).isoformat(), "completed_modules": resume_count})
    progress_path.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
    env = os.environ.copy()
    paths = [build, ROOT] + sorted(p / ".lake/build/lib/lean" for p in cache.iterdir()
                                   if p.is_dir() and (p / ".lake/build/lib/lean").is_dir())
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    start = time.monotonic()
    run_checked([args.lean, "--version"], logs / "toolchain.log", env)
    toolchain = (logs / "toolchain.log").read_text().strip()
    expected_version = (ROOT / "lean-toolchain").read_text().strip().split(":")[-1]
    if expected_version.lstrip("v") not in toolchain:
        raise RuntimeError(f"Unexpected Lean version: {toolchain}")
    for index, source in enumerate(sources, 1):
        if index <= resume_count:
            continue
        relative = source.relative_to(ROOT)
        output = (build / relative).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (str(relative).replace("\\", "_").replace("/", "_") + ".log")
        try:
            run_checked([args.lean, "-j1", f"--root={ROOT}", "-o", str(output), str(relative)], log, env)
        except Exception:
            attempt = len(state["prior_attempts"]) + 1
            history = logs / "attempts" / f"{attempt:03d}"
            history.mkdir(parents=True, exist_ok=False)
            shutil.copy2(log, history / log.name)
            shutil.copy2(source, history / (source.name + ".txt"))
            state["prior_attempts"].append({"stopped_at": relative.as_posix(), "completed_modules": index-1,
                                            "log": str(history.relative_to(logs) / log.name)})
            progress_path.write_text(json.dumps(state, indent=2)+"\n", encoding="utf-8")
            raise
        state["completed"].append({"source": relative.as_posix(), "source_sha256": sha(source),
                                    "output_sha256": sha(output), "log": log.name, "log_sha256": sha(log)})
        progress_path.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
        print(f"[{index}/{len(sources)}] {relative.as_posix()}", flush=True)
    run_checked([args.lean, "-j1", f"--root={ROOT}", "audit/ExactCheck.lean"], logs / "exact.log", env)
    exact_text = (logs / "exact.log").read_text(encoding="utf-8-sig")
    if "Erdos911.erdos_911_full_proof : Erdos911.ExactStatement" not in exact_text:
        raise RuntimeError("The exact target check did not finish.")
    run_checked([args.lean, "-j1", f"--root={ROOT}", "audit/Axioms.lean"], logs / "axioms.log", env)
    axiom_text = (logs / "axioms.log").read_text(encoding="utf-8-sig")
    records = re.findall(r"'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", axiom_text)
    expected = re.findall(r"^#print axioms (\S+)", (ROOT / "audit/Axioms.lean").read_text(encoding="utf-8-sig"), re.M)
    if [name for name, _ in records] != expected:
        raise RuntimeError("Axiom report does not cover exactly the declared audit targets.")
    for name, ax in records:
        if set(filter(None, map(str.strip, ax.split(",")))) - STANDARD_AXIOMS:
            raise RuntimeError(f"Nonstandard axiom dependency: {name}: {ax}")
    run_checked([sys.executable, "audit/check_sources.py"], logs / "source-check.log", env)
    after = {p.relative_to(ROOT).as_posix(): sha(p) for p in sources}
    if before != after:
        raise RuntimeError("A proof source changed during verification.")
    source_check = json.loads((ROOT / "audit/source-check.json").read_text(encoding="utf-8-sig"))
    assert source_check["statement_matches_upstream_ignoring_whitespace"]
    assert source_check["sizeRamsey_matches_upstream_ignoring_whitespace"]
    assert source_check["placeholder_or_added_axiom_scan_passed"]
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "complete_exact_proof",
        "verification_mode": "isolated_clean_source_build_with_verified_resume" if len(state["resume_points"]) > 1 or resume_count else "isolated_clean_source_build",
        "toolchain": toolchain,
        "modules": len(sources),
        "supporting_theorems_audited": len(records),
        "project_build_passed": True,
        "clean_project_build_passed": True,
        "literal_exact_statement_checked": True,
        "full_erdos_911_theorem_proved": True,
        "full_theorem": "Erdos911.erdos_911_full_proof",
        "uses_only_standard_axioms": True,
        "standard_axioms": sorted(STANDARD_AXIOMS),
        "axioms_log_sha256": sha(logs / "axioms.log"),
        "exact_log_sha256": sha(logs / "exact.log"),
        "source_sha256": after,
        "elapsed_seconds_this_invocation": round(time.monotonic() - start, 2),
        "elapsed_seconds": round((datetime.now(timezone.utc) - datetime.fromisoformat(state["initial_started_at_utc"])).total_seconds(), 2),
        "resumed_prefix_modules": resume_count,
        "resume_points": state["resume_points"],
        "prior_attempts": state["prior_attempts"],
        "source_edits_between_attempts": [{"file": name, "initial_sha256": digest, "final_sha256": after[name]}
            for name, digest in state["initial_source_sha256"].items() if after[name] != digest],
    }
    (logs / "validation.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key != "source_sha256"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
