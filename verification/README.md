# Exact-proof verification record

The selected proof is commit **`de87ff8e79ab35bac76c9af70f1a584249052ec1`** on `main` in
[Ghuffy1/erdos911-lean](https://github.com/Ghuffy1/erdos911-lean/tree/de87ff8e79ab35bac76c9af70f1a584249052ec1). Its complete target is
`Erdos911.erdos_911_full_proof : Erdos911.ExactStatement`.

## Actual checks

| Check | Result | Evidence |
| --- | --- | --- |
| Isolated source rebuild | Passed: 437 project modules, no accepted warnings | `clean-build.json`, `module-build-records.json`, `build-log-manifest.json` |
| Literal original-statement check | Passed, with the full real-valued limit and strict conclusion | `exact-statement.log`, `audit/ExactCheck.lean` |
| Axiom audit | Passed for 1546 declarations | `axioms.log` |
| Source correspondence | Full statement and size Ramsey definition match the frozen upstream sources | `audit/source-check.json` |
| Fresh Lean kernel replay | Passed for the complete imported closure of `Erdos911.FullProof` | `replay/leanchecker-fresh.log`, `replay/replay.json` |
| leanchecker-paranoid export check | Passed for the final theorem dependency closure | `export-replay/leanchecker-paranoid.log` |
| lean4lean-import export check | Passed for the final theorem dependency closure | `export-replay/lean4lean-import.log` |
| nanoda export check | Passed for the final theorem dependency closure | `export-replay/nanoda-standard.log` |
| con-leche export check | Passed for the final theorem dependency closure | `export-replay/con-leche.log` |
| con-ron export check | Passed for the final theorem dependency closure | `export-replay/con-ron.log` |
| Deliberately false proof | Rejected, as required | `replay/rejected-false-proof.log` |
| Nonexistent checker target | Rejected, as required | `replay/rejected-missing-target.log` |
| Positive and negative export controls | Every checker accepted a valid control and rejected its deliberately false proof | `export-controls/controls.json` |
| Fresh checkout on GitHub Actions | Passed at the selected proof commit | [Workflow run](https://github.com/Ghuffy1/erdos911-lean/actions/runs/42131466849), `github-ci.json` |
| Hosted version history | Run creation recorded at 2026-11-05T23:42:45Z for the selected commit | `publication-evidence.json` |
| Dependency revisions | All nine matched their locks; no tracked local changes | `audit/dependency-final-check.json` |

The final theorem's transitive axioms are exactly `propext`,
`Classical.choice` and `Quot.sound`. The proof sources contain no admissions,
additional axioms or native decision shortcuts. The original upstream problem
is retained as a text-only reference; its placeholder proof is not imported.

## What was checked

The original local source rebuild completed at 2026-11-05T23:30:14.950025+00:00.
Its output directory did not reuse earlier project oleans. Each accepted
module has a source/output/log hash record, and retained-prefix hashes were
rechecked after correcting style warnings. The completed report records
each restart and its cosmetic source edits; the original warning logs are retained.
The release has only the four
documented comment edits, recorded in `source-correspondence.json`.
The successful GitHub run rebuilds the selected released source in a fresh
Linux checkout, checks the literal target and axiom audit, and runs the Lean
kernel replay. This connects the local evidence to the public proof version.

The later evidence/paper update corrects two phrases in the final documentation
comment of `Erdos911.lean`. All imports, definitions, statements and proofs are
byte-for-byte unchanged; see `documentation-source-change.json`. Every other
Lean file is unchanged. The submitted version remains the explicitly named
proof commit, not an unpinned branch tip.
`audit/release-source-manifest.json` records that selected proof version;
`evidence-source-manifest.json` records the later documentation update.

## Trust and review limits

`leanchecker` reuses Lean's kernel and replays declarations into a fresh
environment; it is not an independently implemented kernel. The additional
checkers consume a dependency-closed NDJSON export of the final theorem.
Lean4Lean, nanoda, con-leche and con-ron are separate checker implementations;
Lean's paranoid checker is a strengthened native-kernel build. Each result is
reported individually above. These are machine checks, not independent human
mathematical review. Negative controls confirm that a false proof and missing
target are not silently accepted.

The initial attempt to run bundled Lean4Lean directly on current `.olean`
files failed with an incompatible-header error; it is retained in
`replay/lean4lean-fresh.log` and is not reported as a pass. The historical
`audit/replay.py` produced that attempt; use the commands in the main README
and the supported export script below for current reproduction. The supported export
commands are taken from the pinned toolchain's `Lake/CLI/Check.lean`. These
direct Windows export checks do not run inside the Linux Lake sandbox.
The first nanoda configuration had its natural-number literal extension
disabled and stopped at a literal. Its later attempt enables the documented
standard `nat_extension`, retaining the same three permitted axioms and
hard errors for any other axiom. Both configurations and logs are retained.
Nanoda's final log reports zero typechecker errors and one diagnostic
pretty-printer error (`Unable to print axioms`); its type-checking exit code
is zero. The diagnostic is preserved in the published log.
The export's hash and size are in `export-replay/export-verification.json`.
Reproduce all export checks after building with:

```sh
python verification/export-replay.py --bin /path/to/pinned/lean/bin --package-cache .lake/packages
python verification/checker-controls.py --bin /path/to/pinned/lean/bin
```

The separate export control changes the type of a theorem proved by
`True.intro` from `True` to `False`. All five checkers accepted the original
control and rejected the corrupted one. The actual Erdős proof was not
modified. Both small control exports and their logs are included.

The source and the manuscript are supplied for mathematical review. These
reports do not certify human authorship, priority, organizer acceptance,
eligibility or an award. The literature search and its scope are documented
in `audit/LITERATURE_REVIEW_20261105.md`.
