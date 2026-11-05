"""Compare the local target and definition with their frozen upstream source."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(relative_path: str) -> str:
    return (ROOT / relative_path).read_text(encoding="utf-8-sig")


def normalized(text: str) -> str:
    return re.sub(r"\s+", "", text)


upstream_statement = re.search(
    r"theorem erdos_911\s*:\s*(.*?)\s*:=\s*by",
    read("audit/upstream-911.lean.txt"),
    re.DOTALL,
).group(1)
local_statement = re.search(
    r"def ExactStatement\s*:\s*Prop\s*:=\s*(.*?)(?=/--)",
    read("Erdos911/Statement.lean"),
    re.DOTALL,
).group(1)
upstream_definition = re.search(
    r"noncomputable def sizeRamsey(.*?)end SimpleGraph",
    read("audit/upstream-SizeRamsey.lean.txt"),
    re.DOTALL,
).group(1)
local_definition = re.search(
    r"noncomputable def sizeRamsey(.*?)end SimpleGraph",
    read("Erdos911/SizeRamsey.lean"),
    re.DOTALL,
).group(1)

statement_matches = normalized(local_statement) == normalized(upstream_statement)
definition_matches = normalized(local_definition) == normalized(upstream_definition)
assert statement_matches, "The local target differs from the upstream proposition."
assert definition_matches, "The local sizeRamsey definition differs from upstream."

files = [ROOT / "Erdos911.lean", *sorted((ROOT / "Erdos911").rglob("*.lean"))]
for path in files:
    source = path.read_text(encoding="utf-8")
    source = re.sub(r"/-.*?-/", "", source, flags=re.DOTALL)
    source = re.sub(r"--[^\n]*", "", source)
    assert not re.search(r"\b(sorry|admit|native_decide)\b", source), path
    assert not re.search(r"^\s*(axiom|opaque)\b", source, re.MULTILINE), path
    assert not re.search(r"\bunsafe\b|\bimplemented_by\b|debug\.skipKernelTC|\bsorryAx\b", source), path

report = {
    "upstream_commit": read("audit/upstream-commit.txt").strip(),
    "statement_matches_upstream_ignoring_whitespace": statement_matches,
    "sizeRamsey_matches_upstream_ignoring_whitespace": definition_matches,
    "placeholder_or_added_axiom_scan_passed": True,
    "full_theorem_declared": "theorem erdos_911_full_proof : ExactStatement" in read("Erdos911/FullProof.lean"),
    "proof_verification_is_separate": True,
    "source_sha256": {
        path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in files
    },
}
(ROOT / "audit/source-check.json").write_text(
    json.dumps(report, indent=2) + "\n", encoding="utf-8"
)
print(json.dumps({key: value for key, value in report.items() if key != "source_sha256"}, indent=2))
