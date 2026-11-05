# Size Ramsey numbers at high average degree

This repository contains a complete Lean proof of **Erdős problem 911**.
The matching Justin Sun Prize catalog identifier is **JSP-000756**.

The final theorem is `Erdos911.erdos_911_full_proof` in
[`Erdos911/FullProof.lean`](Erdos911/FullProof.lean). It proves the exact
statement in [`Erdos911/Statement.lean`](Erdos911/Statement.lean): a real
function whose ratio to the density parameter tends to positive infinity,
with a uniform strict size Ramsey bound for every positive-order finite graph.

The paper is [`paper/erdos911.pdf`](paper/erdos911.pdf), with its
LaTeX source alongside it. No arXiv submission or prize acceptance is claimed.

## Reproduction

Install the Lean toolchain specified in `lean-toolchain`.
The auxiliary audit scripts require Python 3.10 or later and use only its
standard library. Then run:

```sh
lake exe cache get
lake build
lake env lean audit/ExactCheck.lean
lake env lean audit/Axioms.lean
lake env leanchecker --fresh Erdos911.FullProof
python audit/check_sources.py
```

`ExactCheck.lean` writes out the full target independently of its local alias.
The expected axioms of the final theorem are `propext`, `Classical.choice`,
and `Quot.sound`. The source audit compares the exact proposition and the
definition of `sizeRamsey` with the frozen Formal Conjectures sources and
rejects proof placeholders, additional axioms, and kernel-bypass declarations.

For a separate clean source build, using an existing dependency cache:

```sh
python verify.py --package-cache .lake/packages --build-dir .lake/verification/lib/lean --report-dir audit/local-build
```

This rebuilds every project source in import order without using existing
project oleans, checks the literal target and all declared axiom targets,
and verifies that proof source hashes did not change during the run.
Version-specific verification evidence is added under `verification/`.

## Authors and AI assistance

The paper authors and project contributors, in alphabetical order by surname,
are Will Howe ([H0W4RD-dev](https://github.com/H0W4RD-dev)),
Grant Huffman ([Ghuffy1](https://github.com/Ghuffy1)),
Jensen Kohlmeyer ([JENW1N](https://github.com/JENW1N)), and
Liam Kruer ([lkruer](https://github.com/lkruer)). The repository owner is Ghuffy1.

OpenAI ChatGPT and Codex assisted with mathematical exploration, proof
development, Lean formalization, and writing. Human authorship is recorded
as designated by the project team; an independent human referee review is
not asserted by the machine-verification logs.

## Provenance

The statement and size Ramsey definition are from the pinned Formal
Conjectures revision `7a33a65fc13b8ffb12be0fb0388f8d6fd62eb3e8`.
The imported local-lemma development is adapted from Juan Pablo Traverso
Gianini's work, with its original Apache-2.0 header, license, source snapshot,
and provenance retained. See `THIRD_PARTY_NOTICES.md`.

The literature review is [`audit/LITERATURE_REVIEW_20261105.md`](audit/LITERATURE_REVIEW_20261105.md).
It distinguishes the full statement from earlier special cases and partial
work. It does not certify priority, award eligibility, or payment.
