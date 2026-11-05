# Exact-proof verification record

The complete target is `Erdos911.erdos_911_full_proof` in
`Erdos911/FullProof.lean`. The literal target is independently written in
`audit/ExactCheck.lean`.

## Completed clean source build

- Finished: 2026-11-05T23:30:14.950025+00:00.
- Toolchain: Lean (version 4.35.0-rc3, x86_64-w64-windows-gnu, commit 470d5ce1400764999581fd26d5d72b00d990b0f4, Release).
- Project modules: 437.
- Audited declarations: 1546.
- Literal full statement: passed, including all quantifiers and the strict inequality.
- Compiler warnings: none accepted by the verifier.
- Final theorem axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Source hashes: unchanged during each accepted invocation; retained-prefix hashes rechecked on resumption.

The raw report is `clean-build.json`; `module-build-records.json`,
`exact-statement.log`, `axioms.log` and `build-log-manifest.json` preserve
the per-module records, outputs and hashes. The build used
an isolated project output directory and existing dependencies at their locked
revisions; it did not reuse previously compiled project modules.
Style warnings were corrected before resumption. Each already rebuilt prefix
was retained only after its source, output and log hashes matched. The completed
report records every restart and source edit between attempts; the original
warning logs are retained in `resolved-warnings/`.

`source-correspondence.json` records the release's comment-only edits in four
files. All proof code is unchanged from the clean build. Fresh-checkout CI
rebuilds the released files themselves.

Further replay and CI results will be recorded with the exact checked proof
commit, rather than inferred from this source-build report. These records are
machine-verification evidence, not an independent human review, priority
determination, or prize decision.
