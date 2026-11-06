"""Export the final theorem and replay it with the bundled external kernels.

Uses the command forms in the pinned toolchain's Lake/CLI/Check.lean.
This is an additional check of the target's dependency closure, not a
replacement for the clean source build or literal statement comparison.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TARGET = "Erdos911.erdos_911_full_proof"


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--bin", type=Path, required=True)
    p.add_argument("--package-cache", type=Path, required=True)
    p.add_argument("--build-dir", type=Path, default=ROOT/".lake/build/lib/lean")
    p.add_argument("--report-dir", type=Path, default=ROOT/"audit/export-verification")
    a = p.parse_args()
    logs = a.report_dir.resolve()
    if logs.exists() and any(logs.iterdir()):
        raise RuntimeError("Use a new empty report directory; retain earlier attempts.")
    logs.mkdir(parents=True, exist_ok=True)
    sources = [ROOT/"Erdos911.lean", *sorted((ROOT/"Erdos911").rglob("*.lean"))]
    source_hashes = {f.relative_to(ROOT).as_posix(): sha(f) for f in sources}
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["PATH"] = str(a.bin.resolve()) + os.pathsep + env.get("PATH", "")
    paths = [a.build_dir.resolve(), ROOT] + sorted(
        d/".lake/build/lib/lean" for d in a.package_cache.resolve().iterdir()
        if d.is_dir() and (d/".lake/build/lib/lean").is_dir())
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))
    report = {
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "target": TARGET,
        "scope": "Final theorem and its recursively exported dependency closure",
        "source_sha256": source_hashes,
        "source_of_invocation": "Pinned Lean toolchain src/lean/lake/Lake/CLI/Check.lean",
        "export_unsafe": False,
        "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "records": [],
        "limitations": [
            "Direct checker invocations run without a Lake Linux sandbox on this Windows host.",
            "Machine checking does not establish priority, human review, or prize eligibility.",
        ],
    }
    def save() -> None:
        (logs/"export-verification.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")

    suffix = ".exe" if os.name == "nt" else ""
    def binary(name: str) -> str:
        return str(a.bin.resolve()/(name+suffix))

    def run(name: str, cmd: list[str], stdout_file: Path | None = None) -> dict:
        print(f"Starting {name}", flush=True)
        start = time.monotonic()
        log = logs/(name+".log")
        with log.open("wb") as err:
            if stdout_file is None:
                result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=err, stderr=subprocess.STDOUT)
            else:
                with stdout_file.open("wb") as out:
                    result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=out, stderr=err)
        record = {
            "name": name, "command": cmd, "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic()-start, 2),
            "log": log.name, "log_sha256": sha(log),
            "binary_sha256": sha(Path(cmd[0])),
        }
        report["records"].append(record)
        save()
        print(f"{name}: exit {result.returncode}, {record['elapsed_seconds']} seconds", flush=True)
        return record

    export_file = logs/"full-proof.ndjson"
    exporter = run("leanexport", [binary("leanexport"), "Erdos911.FullProof", "--", TARGET], export_file)
    if exporter["exit_code"] != 0:
        raise RuntimeError("Export failed; see its preserved log.")
    names: dict[int, str] = {0: ""}
    declared_names: set[str] = set()
    count = 0
    with export_file.open(encoding="utf-8") as stream:
        for line in stream:
            obj = json.loads(line)
            count += 1
            if "in" in obj:
                v = obj.get("str") or obj.get("num")
                suffix_name = v.get("str", str(v.get("i")))
                prefix = names[v["pre"]]
                names[obj["in"]] = prefix + ("." if prefix else "") + suffix_name
            for key in ("def", "thm", "axiom", "opaque", "quotient"):
                if key in obj and isinstance(obj[key], dict) and "name" in obj[key]:
                    declared_names.add(names[obj[key]["name"]])
    report["export"] = {
        "file": export_file.name, "sha256": sha(export_file), "bytes": export_file.stat().st_size,
        "ndjson_records": count, "requested_theorem_declared": TARGET in declared_names,
    }
    save()
    if TARGET not in declared_names:
        raise RuntimeError("The export did not declare the requested final theorem.")
    config = logs/"nanoda-config.json"
    config.write_text(json.dumps({
        "use_stdin": False, "export_file_path": str(export_file),
        "permitted_axioms": report["permitted_axioms"],
        "unpermitted_axiom_hard_error": True, "num_threads": 1,
        "nat_extension": True, "string_extension": True,
    }, indent=2)+"\n", encoding="utf-8")
    commands = [
        ("leanchecker-paranoid", [binary("leanchecker-paranoid"), "--silent", "--from-export", str(export_file)]),
        ("lean4lean-import", [binary("lean4lean"), "--import", str(export_file)]),
        ("nanoda", [binary("nanoda_bin"), str(config)]),
        ("con-leche", [binary("con-leche"), str(export_file)]),
        ("con-ron", [binary("con-ron"), str(export_file)]),
    ]
    for name, cmd in commands:
        run(name, cmd)
    assert source_hashes == {f.relative_to(ROOT).as_posix(): sha(f) for f in sources}, "Sources changed during checking."
    report["proof_sources_unchanged"] = True
    report["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
    report["all_checkers_passed"] = all(r["exit_code"] == 0 for r in report["records"])
    save()
    print(json.dumps({k:v for k,v in report.items() if k not in ["records", "source_sha256"]}), flush=True)


if __name__ == "__main__":
    main()
