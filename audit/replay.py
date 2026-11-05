"""Replay the full proof closure and check rejection controls sequentially."""
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

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def execute(command: list[str], log: Path, env: dict[str, str]) -> dict:
    start = time.monotonic()
    with log.open("w", encoding="utf-8") as out:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    return {"command": command, "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic()-start, 2),
            "log": log.name, "log_sha256": sha(log)}

def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--lean", default="lean")
    p.add_argument("--leanchecker", default="leanchecker")
    p.add_argument("--lean4lean", default="lean4lean")
    p.add_argument("--package-cache", type=Path, default=ROOT / ".lake/packages")
    p.add_argument("--build-dir", type=Path, default=ROOT / ".lake/verification/lib/lean")
    p.add_argument("--report-dir", type=Path, default=ROOT / "audit/replay")
    a = p.parse_args()
    logs = a.report_dir.resolve()
    if logs.exists() and any(logs.iterdir()):
        raise RuntimeError("Choose a new empty report directory; preserve earlier check attempts.")
    logs.mkdir(parents=True, exist_ok=True)
    sources = [ROOT/"Erdos911.lean", *sorted((ROOT/"Erdos911").rglob("*.lean"))]
    before = {x.relative_to(ROOT).as_posix(): sha(x) for x in sources}
    assert (a.build_dir / "Erdos911/FullProof.olean").exists(), "Build the full theorem first."
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    paths = [a.build_dir.resolve(), ROOT] + sorted(
        x / ".lake/build/lib/lean" for x in a.package_cache.resolve().iterdir()
        if x.is_dir() and (x / ".lake/build/lib/lean").is_dir())
    env["LEAN_PATH"] = os.pathsep.join(map(str, paths))

    control = ROOT / ".lake/replay-controls/InvalidProof.lean"
    control.parent.mkdir(parents=True, exist_ok=True)
    control.write_text("import Erdos911.FullProof\nexample : False := by\n  exact True.intro\n", encoding="utf-8")
    records = []
    bad = execute([a.lean, "-j1", f"--root={control.parent}", str(control)], logs/"rejected-false-proof.log", env)
    rejected = (logs/"rejected-false-proof.log").read_text(encoding="utf-8-sig")
    assert bad["exit_code"] != 0 and "True.intro" in rejected and "False" in rejected, rejected
    bad["expected_rejection_observed"] = True
    records.append(bad)
    print("False-proof rejection control passed.", flush=True)

    missing = execute([a.leanchecker, "--fresh", "Erdos911.ThisModuleMustNotExist"], logs/"rejected-missing-target.log", env)
    assert missing["exit_code"] != 0, "The checker accepted a nonexistent target."
    missing["expected_rejection_observed"] = True
    records.append(missing)
    print("Missing-target rejection control passed.", flush=True)

    kernel = execute([a.leanchecker, "--fresh", "-v", "Erdos911.FullProof"], logs/"leanchecker-fresh.log", env)
    records.append(kernel)
    assert kernel["exit_code"] == 0, (logs/"leanchecker-fresh.log").read_text(encoding="utf-8-sig")[-10000:]
    assert "Erdos911.FullProof" in (logs/"leanchecker-fresh.log").read_text(encoding="utf-8-sig")
    print("Lean kernel fresh replay passed.", flush=True)

    independent = execute([a.lean4lean, "--fresh", "-v", "Erdos911.FullProof"], logs/"lean4lean-fresh.log", env)
    records.append(independent)
    after = {x.relative_to(ROOT).as_posix(): sha(x) for x in sources}
    assert before == after, "A proof source changed during replay."
    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "target": "Erdos911.FullProof", "source_sha256": after,
        "kernel_fresh_replay_passed": kernel["exit_code"] == 0,
        "lean4lean_fresh_replay_passed": independent["exit_code"] == 0,
        "false_proof_rejected": True, "missing_target_rejected": True,
        "records": records,
        "binary_sha256": {str(Path(x).name): sha(Path(x)) for x in [a.lean, a.leanchecker, a.lean4lean] if Path(x).is_file()},
        "limitations": [
            "leanchecker reuses the Lean kernel; it is not an independent kernel implementation.",
            "Lean4Lean is a separate implementation with closely related algorithms, not an independent human mathematical review.",
            "These checks do not establish priority, authorship or prize eligibility."
        ]
    }
    (logs/"replay.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    assert independent["exit_code"] == 0, (logs/"lean4lean-fresh.log").read_text(encoding="utf-8-sig")[-10000:]
    print("Lean4Lean fresh replay passed.", flush=True)
    print(json.dumps({k:v for k,v in report.items() if k not in ["records", "source_sha256"]}), flush=True)

if __name__ == "__main__":
    main()
