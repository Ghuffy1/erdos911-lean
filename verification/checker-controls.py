"""Confirm that each export checker accepts a valid input and rejects a false proof."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--bin", type=Path, required=True)
parser.add_argument("--report-dir", type=Path, default=ROOT/"audit/export-controls")
args = parser.parse_args()
OUT = args.report_dir.resolve()
BIN = args.bin.resolve()
assert not OUT.exists(), "Preserve prior control checks."
OUT.mkdir(parents=True)
build = ROOT/".lake/export-controls"
build.mkdir(parents=True, exist_ok=True)
src = 'import Init\nnamespace CheckerControl\ntheorem trueProof : True := True.intro\ndef falseTarget : Prop := False\nend CheckerControl\n'
(OUT/"Control.lean.txt").write_text(src, encoding="utf-8")
(build/"Control.lean").write_text(src, encoding="utf-8")
env = os.environ.copy()
env["LEAN_PATH"] = str(build)
env["LEAN_NUM_THREADS"] = "1"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(name, args, output=None):
    log = OUT/(name+".log")
    with log.open("wb") as stream:
        if output:
            with output.open("wb") as stdout:
                result = subprocess.run(args, cwd=ROOT, env=env, stdout=stdout, stderr=stream)
        else:
            result = subprocess.run(args, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    return {"name": name, "command": args, "exit_code": result.returncode,
            "log": log.name, "log_sha256": sha(log), "binary_sha256": sha(Path(args[0]))}

def exe(name):
    return str(BIN/(name+(".exe" if os.name == "nt" else "")))

records = []
compile_result = run("compile-control", [exe("lean"), "-j1", "--root="+str(build), "-o", str(build/"Control.olean"), str(build/"Control.lean")])
records.append(compile_result)
assert compile_result["exit_code"] == 0
valid = OUT/"valid.ndjson"
export_result = run("export-control", [exe("leanexport"), "Control", "--", "CheckerControl.trueProof", "CheckerControl.falseTarget"], valid)
records.append(export_result)
assert export_result["exit_code"] == 0
objects = [json.loads(line) for line in valid.read_text(encoding="utf-8").splitlines()]
names = {0: ""}
for obj in objects:
    if "in" in obj:
        v = obj.get("str") or obj.get("num")
        prefix = names[v["pre"]]
        names[obj["in"]] = prefix+("." if prefix else "")+v.get("str", str(v.get("i")))
false_name = next(k for k,v in names.items() if v == "False")
false_expr = next(o["ie"] for o in objects if o.get("const", {}).get("name") == false_name)
mutated = 0
for obj in objects:
    if names.get(obj.get("thm", {}).get("name")) == "CheckerControl.trueProof":
        obj["thm"]["type"] = false_expr
        mutated += 1
assert mutated == 1
invalid = OUT/"invalid.ndjson"
invalid.write_text("".join(json.dumps(o,separators=(",", ":"))+"\n" for o in objects), encoding="utf-8")
results = {}
for name in ["leanchecker-paranoid", "lean4lean", "nanoda_bin", "con-leche", "con-ron"]:
    pair = []
    for label, path in [("valid", valid), ("invalid", invalid)]:
        if name == "leanchecker-paranoid":
            cmd = [exe(name), "--silent", "--from-export", str(path)]
        elif name == "lean4lean":
            cmd = [exe(name), "--import", str(path)]
        elif name == "nanoda_bin":
            config = OUT/("nanoda-"+label+".json")
            config.write_text(json.dumps({"export_file_path": str(path), "use_stdin": False,
                "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
                "unpermitted_axiom_hard_error": True, "nat_extension": True,
                "string_extension": True, "num_threads": 1}), encoding="utf-8")
            cmd = [exe(name), str(config)]
        else:
            cmd = [exe(name), str(path)]
        result = run(name+"-"+label, cmd)
        records.append(result)
        pair.append(result)
    results[name] = {"valid_input_accepted": pair[0]["exit_code"] == 0,
                     "false_proof_rejected": pair[1]["exit_code"] != 0}
    print(name+": "+json.dumps(results[name]), flush=True)
report = {"checked_at_utc": datetime.now(timezone.utc).isoformat(),
    "control_description": "The exported theorem type was changed from True to False, retaining its True.intro proof. Every checker also received the unchanged valid export first.",
    "input_sha256": {valid.name:sha(valid),invalid.name:sha(invalid)},
    "results": results, "records": records,
    "all_controls_passed": all(all(r.values()) for r in results.values()),
    "actual_erdos_proof_modified": False}
(OUT/"controls.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
assert report["all_controls_passed"], "A checker did not pass its positive and negative controls."
