# Verification of the complete Erdős 911 proof

The final theorem is `Erdos911.erdos_911_full_proof : Erdos911.ExactStatement`.
The former missing large-right-block premise is now proved by
`large_right_block_ramsey_statement`; `FullProof.lean` supplies it to the
complete reduction chain. No additional hypothesis remains in the final type.

The isolated clean build passed at 2026-11-05T23:30:14.950025+00:00.
It compiled all 437 project modules, checked the literal full
statement, and audited 1546 declarations.
Each accepted module is tied to its source and output hashes. On resumption,
the verifier rechecks every hash in the retained prefix.
The complete machine-readable report is `audit/clean-full/validation.json`.

## Exact mathematical scope

The proposition and `sizeRamsey` definition match the frozen Formal Conjectures
revision `7a33a65fc13b8ffb12be0fb0388f8d6fd62eb3e8`, ignoring whitespace only.
`audit/ExactCheck.lean` writes out the complete proposition independently of
the local alias and applies the final theorem. This retains:

- A real-valued function whose ratio to the real density parameter tends to positive infinity.
- One density threshold uniform over all positive finite graph orders.
- The original hypothesis `C * n ≤ G.edgeSet.ncard` and strict conclusion.
- Ordinary subgraph copies, disconnected targets and isolated vertices.
- Host graphs of every finite order in the minimum defining the size Ramsey number.

## Proof and trust boundary

The final theorem's transitive axiom dependencies are exactly `propext`,
`Classical.choice`, and `Quot.sound`. These are standard Lean logical axioms.
The source scan rejects proof admissions, added axioms, native decision
shortcuts, unsafe declarations and explicit kernel-bypass settings. The pinned
upstream problem contains an admitted proof; only its statement is used here,
and the upstream file is retained as a text snapshot, not an imported module.

The checker does not certify novelty, human authorship, prize eligibility,
or the organizers' acceptance. Independent human mathematical review is not
claimed. The paper and source are supplied for that review.

## Reproduction

Use the locked toolchain and dependencies, then run:

```sh
lake exe cache get
lake build
lake env lean audit/ExactCheck.lean
lake env lean audit/Axioms.lean
lake env leanchecker --fresh Erdos911.FullProof
python audit/check_sources.py
```

For a clean, sequential rebuild of every project source, with an existing
dependency cache and an empty destination:

```sh
python verify.py --package-cache .lake/packages --report-dir audit/local-build
```

`verify.py` sets a separate project search path, compiles every source with one
Lean worker, rejects warnings, checks the exact target and axiom reports, and
requires identical proof-source hashes before and after each invocation.
Resuming is allowed only from a source/output/log prefix whose hashes match.
`verify.ps1` is a Windows wrapper for the same verifier.

## Corrections incorporated in the manuscript

The candidate-list center lemma explicitly requires an integer `s ≥ 2` and
positive cutoffs. The residual-codegree rectangle lemma retains `q ≥ 1`,
`D > 0`, `ρ ≥ 0` and `T' ≥ 2q`. Their actual uses meet these hypotheses.
The high-degree normalization and large-right-block argument use the constants
of the checked source. Earlier incomplete progress records are preserved
separately from the release; they are not the current proof status.

## Public version and completed checks

The selected proof is `de87ff8e79ab35bac76c9af70f1a584249052ec1` in [Ghuffy1/erdos911-lean](https://github.com/Ghuffy1/erdos911-lean/tree/de87ff8e79ab35bac76c9af70f1a584249052ec1).
See [the final verification record](verification/README.md) for the successful
fresh-checkout CI, native replay, negative controls and individually reported
export-checker outcomes. These later records do not alter the proof files.
