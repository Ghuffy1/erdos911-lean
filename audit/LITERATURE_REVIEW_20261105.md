# Erdős 911: literature and priority review

Review date: 2026-11-05 UTC. The original problem is Erdős 911; the matching
Justin Sun Prize catalog identifier is JSP-000756. These numbers are different.

The review found no earlier complete resolution of the uniform two-color
statement in the primary papers, public records, and returned searches listed
below. This is a bounded search result, not a certificate of first authorship.
The original problem site's page initially returned HTTP 403 through the search
tool, but a direct public fetch at 22:51 UTC succeeded. The live problem page
and its proof-claims page showed zero proof expositions and zero proof claims.
An acceptance, priority determination, or award decision is not claimed.

## Original problem and exact target

- Paul Erdős, *Some of my favourite problems which recently have been solved*,
  North-Holland Mathematics Studies 74 (1982), 59–79, printed p. 78:
  https://www.renyi.hu/~p_erdos/1982-33.pdf
  and https://doi.org/10.1016/S0304-0208(08)70415-8.
  The late addition concerns growth of the size Ramsey number relative to
  edge count and edge-to-vertex ratio, uniformly over finite graphs.
- The frozen Formal Conjectures target is at
  https://github.com/google-deepmind/formal-conjectures/blob/7a33a65fc13b8ffb12be0fb0388f8d6fd62eb3e8/FormalConjectures/ErdosProblems/911.lean.
  Local source comparison checks its full proposition and the separate
  `sizeRamsey` definition, ignoring whitespace only. `audit/ExactCheck.lean`
  writes the proposition out again and applies the complete proof.
  A later live fetch of the default-branch file returned blob
  `bd11e61d0842e69c288f5b151d89582517fe2064`, with the same theorem type;
  the default-branch proof is still an admitted open-problem placeholder.
- The maintainer's community data source is
  https://github.com/teorth/erdosproblems/blob/main/data/problems.yaml.
  The earlier same-day refresh recorded problem 911 as open without a formal
  proof. The official live page now marks the statement as formalized; this
  flag is separate from a completed proof and its proof-claims count is zero.

## Primary mathematical sources reviewed

| Source | Relevant scope | Difference from Erdős 911 |
| --- | --- | --- |
| Erdős, Faudree, Rousseau and Schelp, *The size Ramsey number*, Periodica Mathematica Hungarica 9 (1978), 145–161. https://www.renyi.hu/~p_erdos/1978-48.pdf; https://doi.org/10.1007/BF02018930 | Foundational definition and bounds for several graph families. | The definition is used; bounds for specified families do not prove the required uniform density-dependent gain. |
| Erdős and Faudree, *Size Ramsey functions*, Colloq. Math. Soc. János Bolyai 60 (1992), 219–238. https://korandi.org/docs/misc/setsgraphsnumbers/setsgraphsnumbers13.pdf | Restricted-host Ramsey functions, special families and general elementary bounds; inequality (7) on printed p. 228 gives the classical degree–cover argument and credits Beck. | Restricted host orders and specific graph families do not supply the uniform density gain. The classical bound is credited in the manuscript. |
| Oleg Pikhurko, *Asymptotic Size Ramsey Results for Bipartite Graphs*, arXiv:math/0101197v2; SIAM J. Discrete Math. 16, 99–113. https://arxiv.org/abs/math/0101197v2 | Asymptotics for bipartite blow-ups with a fixed template, including one fixed side of a complete bipartite graph. | Its asymptotic parameters do not give a uniform statement for arbitrary targets with growing degree and both sides unrestricted. |
| David Conlon, Jacob Fox and Yuval Wigderson, *Three early problems on size Ramsey numbers*, Combinatorica 43 (2023), 743–768. https://www.its.caltech.edu/~dconlon/size-ramsey.pdf; https://doi.org/10.1007/s00493-023-00034-7 | Complete bipartite, book, and starburst graphs. Theorem 1.1 gives a lower bound for all complete bipartite graphs; Corollary 1.2 is sharp up to constants for a specified side-size range. | These are structured families, rather than all finite graphs of high edge-to-vertex ratio. The manuscript cites this work without treating it as a full resolution. |
| Louis DeBiasio, *A note on the multicolor size-Ramsey numbers of connected graphs*, arXiv:2404.05856v3, revised April 8, 2026. https://arxiv.org/abs/2404.05856v3 | Theorem 1.1 gives a lower bound proportional to r² times the edge count for non-star connected graphs, for r≥2 and sufficiently many edges. Theorem 1.2 has a different r≥6 hypothesis and a bipartite degree parameter. | Growth in the number of colors does not supply the required unbounded density gain with two colors fixed. The two theorem hypotheses must not be conflated. |
| Draganić, Kaufmann, Munhá Correia, Petrova and Steiner, *Size-Ramsey Numbers of Structurally Sparse Graphs*, Random Structures & Algorithms 68 (2026), e70059. https://doi.org/10.1002/rsa.70059; https://arxiv.org/abs/2307.12028 | Upper bounds using treewidth and related structural restrictions. | Different direction and target classes; the inspected statements do not settle the uniform lower-bound problem. |
| David Conlon, *Combinatorial theorems relative to sparse sets*. https://www.its.caltech.edu/~dconlon/ICBSPaper.pdf | Survey of sparse Ramsey and extremal problems, including results on cubic graph size Ramsey numbers. | The inspected results on bounded-degree examples or random-host thresholds do not assert the universal high-density conclusion. |

The full twelve-page publisher PDF of Bielak's *Remarks on the size Ramsey
number of graphs*, Periodica Mathematica Hungarica 18 (1987), 27–38, was
obtained and its abstract and main-result statements inspected:
https://doi.org/10.1007/BF01849031 and
https://link.springer.com/content/pdf/10.1007/BF01849031.pdf.
Its results concern the cyclomatic number of a host for a path, path size
Ramsey bounds, and stars with short tails. They do not assert the universal
high-density conclusion. Pikhurko's follow-up, *Remarks on a paper by H.
Bielak on size Ramsey numbers*, Periodica Mathematica Hungarica 47 (2003),
195–200, was inspected at https://opikhurko.warwick.ac.uk/E/Pikhurko03pmh.pdf.
Its explicit theorem treats stars with an edge subdivided at most twice,
with linear-in-order bounds; it does not assert a universal high-density
theorem. These are scope checks, not new independent verifications of the
papers' individual proofs.

Publisher abstracts and accessible excerpts of Bielak's *Size Ramsey numbers
for some regular graphs* were also checked, distinguishing the induced bounds
in the 2006 proceedings version from ordinary size Ramsey numbers in the later
paper: https://doi.org/10.1016/j.endm.2006.06.007 and
https://www.sciencedirect.com/science/article/pii/S0012365X08006559.
The located statements concern complete tripartite graphs and restricted
regular-graph regimes; the later excerpt expressly leaves bounds for regular
graphs of sufficiently large order as a question. No full proof of the uniform
Erdős 911 conclusion was found in these inspected portions.

## Earlier public partial work

The GPT-Erdos repository contains public notes attributed in its manifest to
Charlie Karoubi. The file was introduced on January 19, 2026, at commit
`b6eaefa73dfd5fb26c003266caf24e0a6602e77a`:
https://github.com/neelsomani/gpt-erdos/blob/b6eaefa73dfd5fb26c003266caf24e0a6602e77a/data/solutions/911/candidate_solution.md.
Despite its filename, its text explicitly reports the full question as open.
It discusses elementary minimum-degree and vertex-cover bounds, bipartite
examples and bounded-degree context; it does not give a full proof. The linked
three-page research PDF likewise says the question remains open. The manifest
has no recorded manual or formal verification for this item. The direct shared
chat pages could not be read as conversations; the public repository text and
research PDF were inspected instead. These notes are credited in the manuscript.

Patrick White and Claude's report dated July 27, 2026 is explicitly marked
PARTIAL: https://www.erdosproblemaday.com/report/911. It records the uniform
bipartite minimum-degree reduction, a biclique-dominating special case, and a
projective-plane obstruction to using biclique extraction alone. Those partial
observations are prior work and are credited in the paper. The report does not
claim a complete solution. Its own live-status observations are dated July 27,
not November 5; they cannot replace a current live check.

The candidate contribution here is the complete uniform argument, including
component-type entropy, the near-regular and incidence branches, and a
dictionary bound uniform over the number and diversity of large-right blocks.
The initial Lean compilation and literal target check have succeeded. The
release verification report records the later clean-build results separately.

## Additional community-record check

The live erdosproblems.ai problem page was fetched directly on November 5,
2026. It displayed Open and stated that no claim settles the problem. Its
proof-claims area remained at a loading placeholder in the fetched HTML, so
that dynamic list was not certified empty. The underlying public repository
page at `plasma-ai/erdos`, `wiki/problems/ramsey_theory/E0911/_index.md`,
blob `5c0ef15f738d1c068e45e12b42e5be31808b990b`, records `status: open`
and `claim: none`; the inspected problem directory contained only that page.
https://github.com/plasma-ai/erdos/blob/main/wiki/problems/ramsey_theory/E0911/_index.md.
The page's own literature assessment is dated October 8 and its original-site
observations are from September 18. Its older claim that no formal statement
exists is superseded by the frozen Formal Conjectures statement used here.
It is corroborating, dated evidence, not an independent proof of priority.

## Searches and limits

The searches covered combinations of:

- `Erdős 911`, `Erdos 911`, `JSP-000756`, `proof`, `solution`, and `Lean`;
- `size Ramsey` / `size-Ramsey` with `average degree`, `minimum degree`,
  `dense graphs`, `density`, `superlinear`, and `lower bound`;
- recent 2025–2026 results and the multicolor lower-bound literature.

Primary source statements were read for the potentially relevant returned
papers. Irrelevant results on online Ramsey games, induced size Ramsey numbers,
paths, fixed bounded-degree classes, and growth in the number of colors were
not treated as resolutions of the original assertion. Search absence does not
rule out unpublished, inaccessible, recently posted, or poorly indexed work.

A public GitHub code search for `erdos_911` and `Erdos911.lean` returned the
Formal Conjectures open statement, an older `ryantuck/erdos-ai` statement
proposal with admitted steps, its statement-format reviews, and a benchmark
name-mapping file. The older proposal was read at commit
`f5e45cc97f93cd22802b2f1c37f08f0bf7becb86`; it does not contain a proof.
No complete Lean proof was found in those returned code-search results.
This is a search-scope observation, not a guarantee that no such repository
exists elsewhere or on an unindexed branch.

## Justin Sun Prize duplicate review

The current catalog still lists JSP-000756 as Open / Lean No / Eligible No.
It is absent from the inspected MathDB pilot register; the current published
route is the legacy contribution PR workflow. Policy and catalog blob hashes,
query results, and exact source links are saved in
`submission-context.json`.

Searching all open and closed JSP PRs for JSP-000756 returned #3703, #3790,
#3902, #4208 and #5223. Their proposed material does not establish the exact
Erdős 911 statement. In particular, #4208 and #5223 incorrectly map the catalog
identifier to Erdős 756; the maintainer's closing comment on #5223 explicitly
identifies a planar-distance statement mismatch:
https://github.com/TheJustinSunPrize/awards/pull/5223#issuecomment-6517442704.
PR #3902 presents a finite K4 certificate, and #3790 describes only scoped
component certificates. None of these is evidence that the uniform theorem
has already been accepted. Their history should be linked and explained in a
new submission, not deleted or misrepresented.

An exact complete proof, mathematical review, source-ownership evidence,
reproduction, and organizer review remain distinct requirements. Catalog
eligibility fields and an award are determined by the program's review process.
