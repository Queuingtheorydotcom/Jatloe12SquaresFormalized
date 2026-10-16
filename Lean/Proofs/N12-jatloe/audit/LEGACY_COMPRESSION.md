# Compressing the seven replayed exclusions and the 117-to-18 reduction

Initial analysis and subsequent implementation, 10 October 2026. The later measured results below supersede the original data-access limitation. This report still does **not** claim a proven 300,000-line assembly or a final sub-million-line bound.

## Implemented and measured since the initial audit

The authenticated historical union contains **8,732,801 Lean lines** before the remaining incomplete case work. See `ARCHIVE_LINE_COUNTS.json`; file counts alone badly understated compilation/storage cost.

The complete 195-module historical C898 source is now recovered without retaining or expanding its multi-gigabyte source archive. All **25,843 pair-overlap certificates / 206,744 strict axis inequalities** in its thirteen pair steps were exactly rechecked and reconstructed with four row indices and two 2-by-2 determinant solves. There were **zero fallback witnesses**. The old 96,595,850 bytes of rational weights become 1,653,952 bytes of unsigned-16-bit support indices before metadata (8,077,331 bytes in fully named JSONL). The bounded pass took 24.36 seconds and 95,024 KiB peak RSS. This is complete exact producer-side arithmetic evidence; the generated whole-case Lean replay remains unfinished.

`Compact/Core/PairSupport.lean` has independently passed Lean in 6.7 seconds. It verifies coefficient identities, weight signs, constant slack and strictness, then derives the original four-variable affine inequality. Synthesis is untrusted; its entire output is checked.

The complete C898 initial enclosure has been translated to **124,996 lines / 5,882,607 bytes / 62 modules**, after per-angle row sharing. It preserves all 704 angle roots, both children of 14,088 cuts, 10,149 genuine empty certificates and 1,121 leaves. The shared `RegionDAG` soundness proof has passed Lean; the full initial-data family has not yet passed. The fifteen later transitions, original owner/case bridge, and whole-exclusion replay remain necessary.

Evidence: `c898-all-pair-support-reconstruction.json`, `evidence/c898-initial-conversion.json`, and `COMPLETE-PROOF-SIZE-BUDGET.md`.

## The expensive part is generated propagation data

The seven accepted author-replay closures contain 938 historical modules / **2,119,721,626 bytes**. Of those, 791 `Push*Chunk` / `PushAuxTree*Chunk` modules contain **2,117,897,276 bytes (99.914%)**. All other historical geometry, angle data, checker soundness, ownership, wrappers and foundations together occupy **1,824,350 bytes**.

| Generated family | Modules | Source bytes |
|---|---:|---:|
| Push717 | 161 | 458,282,056 |
| Push979 | 161 | 330,039,653 |
| Push713 | 93 | 264,669,338 |
| Push973 | 75 | 216,979,993 |
| Push978 | 74 | 208,200,342 |
| Push898 | 66 | 186,698,185 |
| Push701 | 57 | 162,784,107 |
| Shared Push972 | 41 | 114,941,760 |
| Shared Push975 | 28 | 77,859,250 |
| Two PushAuxTree976 families | 35 | 97,442,592 |

For the 117-to-18 closure, **1,468 Push modules alone occupy 2,967,743,905 bytes**. Its other large families are ContinuousScout (229.60 MB), ContinuousUnion (115.60 MB), Continuous (111.74 MB), Region (107.28 MB), Recovery (94.24 MB), Incoming (42.64 MB), Overlap (25.61 MB), and Leaves (23.13 MB). Ordinary proof code is not the main storage problem.

The union of the 117-to-18 reduction and the seven exclusions is **8,236 historical modules / 5,660,148,876 bytes**. Their intersection is 198 modules / 194,243,497 bytes. Thus the old module cap nearly fits this incomplete combined proof while concealing over 5.6 GB of source. Add the 15 completion wrappers when counting the full original local-module union.

## Exact checker schemas already available

The seven replay receipts include `S12.AxisOverlapCertificate`, `S12.ContinuousPruning`, `S12.IndexedContinuous`, `S12.IndexedFarkas`, `S12.RegionTree`, `S12.PoseRegion`, `S12.OrientedCoverage`, and chord-pruning/checker modules. The original `AxisOverlapCertificate` source was inspected directly. Its data are:

1. Two checked rational reference squares.
2. Two lists of center-plane constraints, one for each owner.
3. Eight target signed separating-axis inequalities.
4. A list of Farkas witnesses, each expressed as rational weights on four-dimensional affine constraints.

`AxisOverlapCertificate.sound` proves geometric interior overlap from those eight implications. Its general `Check` searches the witness list for each target. `PruneBlock.Check` matches a certificate for every remaining neighbor pose. `PosePruning` combines forbidden blocks with a complete region-cut tree; `CertifiedPosePruning` combines the cut leaves with relaxations to a target domain. The correctness conditions already contain the required universal coverage and boundary semantics.

The relocated C1090 source gives a directly readable instance of the old indexed format: `Axis1090Batch0.lean` contains 16 separate candidate/checked theorem blocks, each with eight arrays of large integer multipliers and source/neighbor/target references. Its `IndexedKernel.lean` checks sign, strictness, all four coefficients and constant, and proves the scalar checker sound. This sample is **not one of the seven replayed case chunks**, so its statistics cannot be extrapolated as a measured reduction factor for them.

The C976 exporter independently shows the repetition mechanism: for every source leaf, it builds a block; for every neighbor leaf, it writes a separate `AxisOverlapCertificate` with eight witnesses; then it emits the block certificate, tree, relaxation links, complete plan and coverage proof. Source center constraints are carried inside each pair certificate even when the algebraic witness does not use them. Small domain/hash modules do not remove this source-leaf × neighbor-leaf × axis product.

## What cosmetic compression actually saves in the inspected sample

The inspected 50,180-byte C1090 batch contains **128 witness rows / 744 multiplier-index terms**. Normalizing each nonnegative integer weight vector by its positive gcd reduces its serialized weight text from **28,196 to 26,152 characters (7.25%)**. After that normalization, 124 of 128 rows remain distinct. The 16 theorem boilerplates account for some additional removable text, but these measurements do not support a factor-100 reduction from deduplication alone.

Large numerators are therefore not all redundant common scales. Some still contain dozens of digits after gcd normalization. Merely shortening names, removing whitespace, using archives, or placing many values on a line would fail the user's compilation-efficiency objective.

## A concrete semantics-preserving compression route

### 1. Canonical rows and a shared acyclic expression table

Represent a plane row as integer coefficients `(a,b,c)` plus its strictness bit. Clear denominators with a **positive** common multiplier and divide by a positive gcd. Do not flip the sign to force the first coefficient positive: that reverses the half-plane. Do not merge strict and non-strict rows. Prove one conversion lemma from this representation to the original rational `LinearConstraint` semantics.

Pool repeated primitive directions, rows, angle references, ordered domains, and branch nodes. A changed domain refers to its predecessor plus explicit row/pose updates. Actual array indices, not unverified hashes, select Lean data; every out-of-range lookup fails. Existing certificates are translated and rechecked against their new indices. Hashes may help the untrusted producer find duplicates but do not become proof premises.

This removes repeated center polygons and constant state snapshots. It is not yet a bound on the number of distinct rows or transitions.

### 2. Replace four-variable pair witnesses by reusable two-variable supports

For each neighbor polygon and primitive direction, prove one bound

`lower ≤ nx * centerX + ny * centerY`.

A two-dimensional polygon support can be proposed using one active row or a pair of active rows. Store the one or two **row indices**, not its expanded huge rational weights. Reconstruct the weights with exact Cramer's rule, or preferably check equivalent cross-multiplied integer identities and denominator signs. Every proposed basis is still checked; no unproved claim that every basis is adequate enters the theorem.

For an axis recipe, a strict source block row plus that support bound and a nonnegative rational slack imply the required strict axis gap. Check the support once and reuse its proved bound across all source poses of the same angle, all source blocks that use it, and positive multiples of the primitive direction. Reuse a parent support bound for a smaller child domain through an explicit inclusion/monotonicity proof.

This mathematical factorization already exists as source in `Completion/Cases/C976/CompactSupport.lean`:

- `NeighborSupport.ofBasis`, `.ofSingle`, `.Check`, `.sound`;
- `strict_gap_of_support`;
- `AxisRecipe.sound`;
- `SupportBlock.sound`, whose type deliberately omits source-pose center constraints.

The new proof should lift this reusable idea out of a case namespace and verify it once. Its current source is not itself proof acceptance. Crucially, some general old affine witnesses might use source constraints essentially; those require either the generic indexed Farkas fallback or a newly justified source-independent block. Do not silently assume every old certificate has this simpler form.

### 3. Preserve the full trace with one replay theorem and state deltas

Use constructors for initial coverage, relaxation, support-based pair pruning, wall chord pruning, compulsory-point refresh, complete closed split, symmetry transport and contradiction. Every constructor has one soundness proof. An acyclic replay table records references and local modifications; its universal soundness theorem composes them.

Keep strict ownership and complementary split ties. Check every source pose, every remaining neighbor needed by a pruning block, every retained cut leaf and both split children. `CompactPair.Action.Check`, `CompactPruning.CoverCheck` and `CompactPruning.Plan.Check` already show those coverage obligations. Reject short lists and missing target references. Batching must not turn a quantified coverage requirement into a sampled assertion.

Do not repeatedly normalize the same rational checks through transparent giant definitions. Export bounded checked support/domain facts once and reuse their theorems. Checker/chunk boundaries should follow actual reusable facts rather than create one module per numerical witness.

### 4. Shorten the actual mathematical dependency graph

Backward-slice from the final empty domain/strict-owner conflict. Retain only domain changes and witnesses on that contradiction's dependency graph. Whole-domain histories include unrelated changes and exploratory actions. Prove replay over a sliced dependency graph so omitting an unused state update is justified, rather than erasing steps from an imperative trace by intuition.

Next combine repeated propagation cycles into simultaneous inequalities or stronger support cuts. This can remove transitions, but requires a fresh mathematical certificate; ordinary deduplication alone does not prove a shorter cycle. A fixed point or finite cyclic graph may not be accepted merely because it numerically stabilized.

### 5. Rebuild the seven exclusions and later classification from the compact evidence

The actual old theorem statements remain the acceptance targets. The seven existing scoped receipts remain valuable regression evidence; they are not imported as external axioms or omitted dependencies. Replace their generated dependency subgraphs with compact proofs, reconnect row/family identity, and then check each whole exclusion. Rebuild the large 117-to-18 classifier similarly, or bypass it using the small verified 117-case foundation plus a compact exhaustive exclusion table. Either route must account for every retained row.

## A honest size bound needs these currently missing quantities

Let `R` be distinct canonical rows/angle records, `S` distinct polygon-direction support bases, `B` unique source-angle forbidden blocks, `D` domain/update records, `T` replay and branch nodes, and `F` unavoidable generic Farkas terms after the support conversion. A source layout with one bounded record per line has a constructive budget of roughly

`fixed proof code + cR*R + cS*S + cB*B + cD*D + cT*T + cF*F`.

The constants can be fixed by the serializer and measured on real output. C898 initial records and its complete pair witnesses are now inventoried. **The complete seven-case union and baseline R/S/B/D/T/F totals remain unknown**. No source-size argument derived only from 791 chunk files determines them. In particular the neighbor-support Cartesian product may still be large even when all mathematical code is generic.

The exact missing evidence is:

- A selectively accessible copy or byte index for the authenticated generated `Push` chunks and the original exporter's dependency graph. Git stores them inside a **single 4,066,975,006-byte tar+zstd stream**, split into parts; the source manifest records size/hash/source-archive name, but no compressed seek offsets or imports. The initial read-only audit did not stream this archive. A subsequent bounded selective streaming recovery obtained all C898 source and authenticated partial numerical data. No full archive is retained locally; most other-case numerical data are still missing.
- A source-level or trace-level inventory of unique rows, supports, block signatures, state transitions, split nodes, and Farkas fallback witnesses after deterministic translation.
- A complete hardest-case compact replay preserving every endpoint and a measured size/verification cost. A low line count without bounded serialized bytes and repeated-reduction cost is insufficient.

For a defensible **300,000-line assembly**, reserve a fixed small allowance for the already ~9,000-line foundation and common soundness library, and make the remaining record sum an enforced build condition. A **sub-million-line finished proof** additionally needs per-obligation certificate budgets summing below the remaining allowance. Until the counters above are obtained, any claimed factor or final cap would be a target rather than a justified estimate.

## Recommendation

Reuse the compact verified 117-case foundation. Prioritize one full compact translation of a replayed unsplit case (C898 has the smallest measured seven-case closure), using support-basis certificates and state deltas, followed by the largest unsplit case and a split/refresh case. The output must establish the original whole-case theorem and show real reductions in records/bytes/check time. If support reuse still leaves excessive data, return to symbolic propagation-cycle lemmas before translating more cases. Do not start by copying 2.12 GB of previously checked source into the new default build.

Evidence: `BRANCHES.md`, `branch-heads.json`, `replay-closure-sizes.json`; pinned original `S12/AxisOverlapCertificate.lean`; current `CompactSupport.lean`/`CompactPruning.lean`; and [C1090's inspected indexed sample](https://github.com/EvolvingPrograms/SquaresLean/blob/80220fca8a8ca90f4df2c3aea8cf7468dc1285cb/projects/n12-jatloe419/Completion/Cases/C1090/Research/Axis1090Batch0.lean).
