# Complete n=12 obligation inventory

Audit snapshot: 10 October 2026, 20:26 EDT. This document combines all 19 remote branches, the two new progress ZIPs, earlier supplied partial-work packages, and the resident refactor sources. It distinguishes authenticated source, inherited Lean receipts, numerical research, and actual whole-case exclusions. This audit runs no Lean, proof search, certificate replay, or archive-wide extraction. The root worker's concurrent narrow validation is a separate activity, recorded in `.verification/`.

**The unrestricted theorem is unfinished. Seven of the eighteen late cases have inherited successful whole-case Lean receipts. Eleven remain without accepted whole-case exclusions. The earlier reduction from 117 cases to those eighteen is itself not freshly accepted.** A refactor cannot just fill eleven small holes while ignoring the large dependencies behind the already checked seven and the 117-to-18 reduction.

## 1. Exact target and trust boundary

The original target is `S12.packingConstant12 = 4`, with `packingConstant12` defined as the infimum of positive container side lengths admitting `S12.UnitPacking L`. The definition quantifies over twelve arbitrary real-oriented unit squares with disjoint strict interiors; boundary contacts are allowed. It is not an axis-aligned, fixed-angle, sampled, or locally rigid packing theorem.

`vendor/S12/Normalization.lean` maps every hypothetical packing with `0 < L < 4` to the unchanged `S12.NormalizedPacking`: twelve congruent squares inside `[0,4]²`, common side `1 < a ≤ 1001/1000`, unchanged orientations and disjoint strict interiors. `vendor/S12/PackingConstant.lean` contains the side-four construction and the conditional theorem reducing optimality to exclusion of **all** such normalized packings. `Completion/Contracts.lean` requires `ExcludesCase id` for every retained row carrying that ID and every actual packing with that row's marker family.

The pinned original project uses Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Original source provenance is recovery commit `98ddf88a36d0a227d1a94e1c7e0ed64d1c840de8`; the integration checkpoint is `e122bc2b9329da8057ca208343436a380ab97c59`.

Inherited foundational and seven-case receipts include `Lean.ofReduceBool` alongside standard `propext`, `Classical.choice`, and `Quot.sound`. The original source audit identifies 723 historical `native_decide` sites. Thus these receipts carry inherited compiler trust; they are not a claim that every historical arithmetic computation was reduced by the kernel alone. No admissions, new axioms, hidden assumptions, replacement packing model, or unverified imported facts are acceptable ways to finish. The new small conditional interfaces are obligations to be inhabited, not axioms asserting completion.

## 2. Foundations versus the later reduction

| Obligation | Actual evidence | Remaining work |
|---|---|---|
| Construct twelve unit squares in side four | Inherited successful foundational replay includes `S12.packingConstant12_le_four`. | Preserve exact definitions and validated source. |
| Normalize arbitrary smaller packings | Included in original foundational closure. | No new mathematical normalization assumption needed. |
| Exhaustively classify normalized packings into 117 retained rows | Inherited successful 63-module replay includes `S12.unit_packing_reduction_to_117`, with genuine geometric coverage. | Preserve this small boundary and its trust disclosure. |
| Reduce those 117 rows to the later eighteen | Full historical source closure exists: 7,496 modules, 3,734,670,747 source bytes. No completed fresh replay of `S12.CurrentReduction` was found. | Compact/reprove all required exclusions and coverage, or bypass this reduction by proving all 117 row exclusions from the verified foundation. |
| Exclude all eighteen late cases | Seven inherited author receipts; eleven incomplete/unaccepted cases below. | Rebuild compact faithful versions of the seven and finish all eleven, then supply global coverage and assembly. |
| Unconditional `packingConstant12 = 4` | Only conditional assembly theorems exist. | Supply actual inhabitants of every assumption and run complete closure/axiom validation. |

The 63-module foundational closure is exactly 62 historical modules plus `Completion.Contracts`: **1,105,833 bytes / 8,964 newline-counted source lines**. Existing source hashes were checked against the pinned receipt; four small absent sources were read from their pinned Git blobs to complete the count. This is an appropriate small preservation boundary. It is not the same proof as the 7,496-module later reduction.

The eighteen IDs are `696, 701, 709, 713, 717, 898, 973, 974, 976, 977, 978, 979, 981, 983, 1089, 1090, 1091, 1092`. The new `Compact/Assembly/Frontier.lean` expresses both legitimate paths: a complete 117-row exclusion family, or a genuine all-packing reduction to those eighteen plus their exclusions. It supplies neither missing family.

## 3. Every late case, without counting local lemmas as exclusions

“Inherited PASS” below means a pinned author receipt for `excluded : ExcludesCase ID`, whose source identity was audited. It does not mean this audit reran Lean. Independent row/nonvacuity checks exist; independent full replay of all seven geometric proofs is still pending.

| Case | Strongest completed or source-written obligation | True remaining boundary |
|---:|---|---|
| **696** | Earlier package has successful receipts for arbitrary-rotation side-sign geometry, its four transports, conditional finite auxiliary uniqueness, corner separator narrowing, and scalar negative-face transfer. All 13 source hashes match that receipt. Local source writes one residual root and part of the other. | The two correctly decoded residual contexts remain unaccepted; the second root's propagation is incomplete. Domain necessity/entrance, every retained action or its symbolic replacement, and terminal contradictions must all connect to actual packings. A precise compact root-one target is described below. |
| **701** | **Inherited whole-case PASS.** | Compact the actual dependency closure and revalidate its whole exclusion. No new missing case mathematics is recorded, but a tiny wrapper does not preserve a small proof. |
| **709** | Checkpoint contains complete proposed initial coverage, 36 pair operations and four strict border transfers leading to contradictory ownership. | Full Lean replay/repair and compact representation. The earlier eight-point appendix is the same route, not another completed proof. |
| **713** | **Inherited whole-case PASS.** | Compact actual dependencies and revalidate. |
| **717** | **Inherited whole-case PASS.** | Compact actual dependencies and revalidate. |
| **898** | **Inherited whole-case PASS.** Earlier worker draft is superseded by integration. | Compact actual dependencies and revalidate. |
| **973** | **Inherited whole-case PASS.** | Compact actual dependencies and revalidate. |
| **974** | Complete proposed initial coverage and two entrance exclusions in the checkpoint. | Six entrance exclusions still required, including their complete auxiliary ownership coverage; existing new source is unaccepted. The earlier three-square symbolic transfer can shorten selected tails only after its entrance premises are established. |
| **976** | Latest worker branch has full source assembly for **all eleven** residual vectors, unlike the separate six-residual compact checkpoint. Original reduction eliminates 87 of 98 auxiliary vectors in historical source. | No full residual/case Lean replay. The eleven residuals occupy 166,074 archived modules / 7,009,904,025 bytes and cannot be adopted unchanged under the efficiency target. Replace the route compactly, certify all retained ancestry and all children, then accept the complete case. |
| **977** | Inherited focused 76-module replay proves the actual-packing reduction to 16 wall branches and 57 complete ownership vectors. New ZIP adds three small helpers with twenty recorded standard-axiom declaration checks. | **Zero new whole continuous contexts are excluded.** Need initial all-angle coverage, sound operations, all remaining ownership/split coverage, terminal contradictions and complete assembly. The 912 products are represented by a 22-root research plan, not 912 independent long proofs. |
| **978** | **Inherited whole-case PASS.** | Compact actual dependencies and revalidate. |
| **979** | **Inherited whole-case PASS.** | Compact actual dependencies and revalidate. |
| **981** | Latest source connects 62 of 117 diagonal representatives, covering 118 of 221 distinct assignments. This source is uncompiled. The earlier eight-representative shared argument is already included in those 62. | Prove the 55 remaining representative exclusions (103 assignments), accept the existing 62, and discharge complete vector/diagonal coverage. New V108 strip modules and V75 research do not close any additional representative. |
| **983** | Domain source plus a conditional context-assembly interface. Pinned non-Lean route describes 37 contexts covering 941 vectors. | Complete actual-packing context coverage and exact geometric certificates, with all operations and split children justified; no whole-case `Proof.lean` is complete. |
| **1089** | Worker branch contains both row identity and wrapper applying saved `S12.case1089_shared_impossible`. Checkpoint alone omits the row file. | Assemble both files, inspect the true historical dependency closure, compact if needed, and replay. No whole-case acceptance receipt was found. This may be primarily a source/verification boundary rather than new geometric research. |
| **1090** | Historical row/family focused receipts. Source proposes initial coverage and a first-four-step prefix. Route-preservation branch adds evidence, not a second Lean implementation. | Accept the actual 12-owner coverage/bridge, complete the continuation and terminal contradiction. The later 23-step plan lists 531 missing dependencies; source preservation does not prove them. |
| **1091** | Domain data and generic complete-certificate assembly interface. | Supply the actual certificate. Current `Proof.lean` imports missing `C1091.Exclusion`; an interface that would accept a complete certificate is not that certificate. |
| **1092** | Local pinwheel/frame source plus four recovered wall-polynomial drafts. Draft uniform arguments target 48 of 72 face systems; no successful receipt exists for those drafts. | Remaining 24 `P_face = 0` systems; exact polynomial identities/signs/closed interval coverage; face decomposition; center localization and full packing entrance; residual-parent/35-bin ancestry and final case assembly. |

The seven recorded whole-case successes account for a union of **953 local modules**, including 938 historical modules with **2,119,721,626 source bytes**, plus 15 completion wrappers/contracts. This is a real proof-preservation cost. The shared union of the historical 117-to-18 reduction and these seven historical closures is **8,236 modules / 5,660,148,876 bytes**; adding the 15 completion modules gives 8,251 local project modules before finishing the other eleven cases. These are exact pinned-manifest counts, excluding Lean/Mathlib dependencies and compiled objects, not estimates of current disk occupancy.

## 4. ZIP contributions and exact deduplication

### Latest C977 ZIP

Archive SHA-256: `971b2d265c732b43675589a16c9165aea3f1a61cd8546e66d98a7c1a5bd50eb7`. All 301 manifest entries match. The 13 committed case modules are 88,854 bytes / 1,818 lines, pinned to branch `n12/worker-codex-c977-20261010`, commit `cbe674ec39981107208d84d4c15eb29754fe897e`. `continuation/checked/{BorderPoints,WallChains,PoseEnclosure}.lean` adds 16,806 bytes / 373 lines, matching `continuation/evidence/continuation-helper-replay.json`. These are inherited standalone successes, not a new combined replay. Three separate drafts are explicitly unverified and must not be counted as checked work.

The research plan contains 5,619 operation selectors; exact common-ancestor identification removes 1,206 duplicated selectors, leaving 4,413 before further minimization. `evidence/c977-plan-dag.json` records the compact structure. That DAG is not yet a checked geometric trace. The algebraic wall-chain argument is a useful general replacement for selected operations, conditional on SAT and actual enclosure premises; it is not a complete context exclusion. See `audit/C977.md`.

### Latest C981 ZIP

Archive SHA-256: `b51a47bfc4c6c214303c5f016d6f0ad47ae0e9a6cd5fcee468df572059c7434d`. All 497 payload-manifest entries match sizes/SHA-256 and declared Git blob hashes. Exact source recount confirms 117 representatives / 221 assignments, with **62/118 source-connected** and **55/103 pending**. “Source-connected” does not imply Lean acceptance.

`Completion/Cases/C981/CaseVectors.lean` has SHA-256 `12cec78e2c2b46fe4d6ffcc1fcddb2bd216a0a5c50600e76b0ebede9d4ec21c8`; `Remaining.lean` has `36758317fe197703e161c81cbbf478e5dc29454ee4836480b42eb080c211a7cd`. The latter imports `SharedExclusion` and uses it in its resolved predicate, so representatives 9–14, 17–18 must not be added a second time.

The three new `PartialStrip*` modules refine V108's conditional interface; they still require incoming certified owner coverage. V75's proposed empty-domain calculation has no Lean ancestry. V114 cannot inherit V110's entrance unchanged; a relaxed-domain witness blocks that implication. The revised skeleton groups all 55 missing representatives by mathematical rule, rather than treating one conditional generic lemma as 55 completed cases. See `audit/C981.md` and `audit/C981-evidence.json`.

For assembly, this audit copied exactly eight small original Completion modules (38,649 bytes / 756 lines) into the refactor: `CaseVectors`, `OwnershipDomains`, `DiagonalAuxiliary`, `Ownership`, `DomainReuse`, `CornerReduction`, `RowIdentity`, `Geometry`. `Completion/Contracts.lean` was already identical. `evidence/c981-catalogue-imports.json` records archive/member/file SHA-256/Git hashes and every external import. No generated `Remaining` source or large trace was copied. This source copy is not a build receipt or proof that all historical imports are present.

### Earlier result and recovery packages

All **34 files** of `C696-result.zip` and all **12 files** of `C981-shared-exclusion.zip` match their duplicated `current/.../result` copies in `12-square-formalization-partial-work.zip` byte for byte. These are one contribution each, not three independent results. `audit/earlier-package-source-inventory.json` records every Lean member hash and the comparison scope.

The C696 receipt's 13 source hashes match, with recorded exit code zero. It covers seven baseline modules, five canonical proposal modules and a verification wrapper; it does not close either residual root. The source's correct sign-12 convention is `Y8≥2, X9≥2, Y10≤2, X11≤2`; excluding the reversed handoff convention would not close the intended branch.

The earlier C981 package's four-owner/chord argument covers eight representatives and their reflections in its exact numerical model. Its sole 96-line Lean ownership module was uncompiled. The latest C981 package already incorporates that route, as explained above.

The recovered C1092 drafts live under `12-square-formalization-partial-work/current/C1092/`:

| Path | Bytes / lines | SHA-256 |
|---|---:|---|
| `c1092-wall/WallPolynomial/Definitions.lean` | 2,151 / 55 | `253756af3e35b255efb773849290dbfdaf27947c48038823ec99e9cf96fa059e` |
| `soundness/Weighted.lean` | 2,270 / 56 | `9ac267d9054a1d30acaa4a1cee34295287d5dee8eae5cb9d17c7d0d53a93fc40` |
| `soundness/Uniform.lean` | 3,641 / 80 | `0184c75a8a0a69f76a60a1e8d417a9147e65f61124a84b51e6a4b10b6464d58b` |
| `algebra_analysis/UniformP2.lean` | 3,138 / 76 | `795775e1230cbd9f8d1f4c8b1627269b6b5fa9c91d5b52e2707a0b1c00359c97` |

Saved certificate reductions change 128 interval leaves to 98 and then 85 for the same 72 systems. Those are structural research counts, not Lean acceptance.

### Earlier symbolic research

`s12-earlier-case-shortcuts.zip` supplies exact research routes for 59 earlier cases eliminated before the late eighteen; their IDs are disjoint from the eighteen. Twelve of those 59 share a four-square/five-pair template. Therefore this package offers a compact replacement for part of the costly **117-to-18 reduction**, not additional closure among the seven or eleven late cases. It contains no Lean sources.

`s12-density-and-signs.zip` supplies a three-square transfer lemma and checked numerical applicability claims for selected C696/C974/C977 terminal states. It shortens tails conditionally; the entrance still must be proved. It contains no Lean sources. Its density experiments do not produce a new exclusion.

The `s12-proof-complete.zip` title describes non-Lean research material. Its nested source manifests contain no Lean files. Its huge research snapshot was not expanded, and its published geometric dependencies are not automatically formalized. See `audit/LOCAL_RESEARCH.md` for exact paths, inspected mathematical hypotheses, and limitations.

## 5. Concrete mathematical compression achieved or identified

1. **Preserve the verified 117-case foundation.** It is under 9,000 lines and already proves the correct universal packing entrance. Start all shorter routes there; do not import a multi-gigabyte later reduction under a small wrapper.
2. **Prove shared support and geometric rules once.** Existing source already exposes Farkas implication, support-basis soundness and complete pose coverage. Canonical integer halfplanes, shared direction/angle data, indexed one/two-row support bases, state deltas and a sound derivation DAG can replace repeatedly printed before/after polygon states. Ninety-nine-point-nine percent of the seven-case historical bytes are generated Push/PushAuxTree chunks. This is a concrete target, but global compact support counts have not been measured.
3. **Use the earlier shared chord routes for baseline cases.** The 59-case shortcut corpus avoids old branch expansion; twelve cases share one four-square template. All original marker/cover entrance premises and closed orientation intervals remain obligations. These are substantial genuine opportunities for the previously unaudited baseline cost.
4. **C696 has an explicit coupled scalar target.** At the saved root-one state 54, the terminal argument lacks only the owner-10 chord bound `98X + 49(C+S-2CS) - 347 ≥ 0`, with `C²+S²=1` and nonnegative absolute components. That inequality is false on the owner's relaxed state-54 domain alone: pair geometry is necessary. Owner-10/owner-7 action 96 makes the sufficient terminal tests pass at state 97. A direct geometric proof of this one bound and a compact entrance could replace many full-domain updates. Neither is yet proved; the exact bounded probe does not certify ancestry. See `audit/C696-TERMINAL.md`.
5. **C977 shares derivation ancestors and admits an algebraic wall-chain rule.** The exact 1,206-selector reduction is established at the plan level. The new rule reduces variation in selected near-axis normals to a telescoping endpoint inequality. Its SAT/enclosure bridge and applicability must be checked before it closes any context.
6. **C981 shares strict-point/chord endpoints and vector coverage.** The scalar positive endpoint argument and original-square bridge are small source candidates. The 55-vector partition exposes complete obligations; it does not assume the existing 62 are accepted. Some tempting reuse implications are demonstrably false, so a universal success/size claim is premature.

The proposed structure is materially different from generating one source module per pose or transition. It still requires exact certificate instances and complete all-angle/split/ownership coverage. Sparse numerical discovery, existing PASS flags, or finite list completeness alone cannot supply those premises.

## 6. Size inventory: exact scope, no fabricated global line count

All line counts below count newline bytes. “Unavailable” means the source lives in unexpanded archives or only metadata was read, so no exact line count was established. Rows overlap and must **not** be summed.

| Corpus | Modules / `.lean` files | Source bytes | Lines | Scope |
|---|---:|---:|---:|---|
| Inherited foundational closure | 63 | 1,105,833 | 8,964 | Exact dependency/source count, successful inherited scoped receipt. |
| Seven accepted historical exclusions' union | 953 incl. 15 completion | 2,119,721,626 historical bytes, plus small completion files | 5,121,803 historical lines | Actual streamed source counts; every source hash matches. Completion wrappers separate. |
| Historical 117-to-18 reduction | 7,496 | 3,734,670,747 | 3,817,003 | Actual streamed source counts; no fresh completed replay. |
| Union of those two historical corpora | 8,236 historical | 5,660,148,876 | 8,732,801 | Shared modules counted once; completion wrappers separate. |
| Git-visible checkpoint project `c5c6144` | 1,223 | 1,078,483,643 | Not measured | Entire Git-visible project only; excludes archived source payloads and untracked local C696. |
| Local C696 source reported by independent resident audit | 633 | 244,348,554 | 2,496,993 | Source-written, partly unfinished; not an accepted proof. |
| C976 all-eleven archived residual source | 166,074 | 7,009,904,025 | Unavailable | Exact eleven manifests; all say `lean_compiled: false`. Alternative to checkpoint's separate compact attempt. |
| Latest C977 committed case modules | 13 | 88,854 | 1,818 | Focused reduction, not full geometric closure. |
| Latest C977 checked helper additions | 3 | 16,806 | 373 | Inherited standalone receipts, not whole-case checks. |
| Latest C981 case source | 136 | 106,652,779 | 968,001 | Exact ZIP bytes; source-connected 62/117 only, uncompiled. |
| All resident Lean source in latest C981 ZIP | 292 | 108,058,713 | 983,353 | Includes dependencies and other source; overlaps preceding row. |
| Earlier C696 result ZIP | 13 | 53,701 | 1,283 | Baseline + five new helpers + wrapper; not a C696 exclusion. |
| Earlier C981 result ZIP | 1 | 3,702 | 96 | Uncompiled ownership helper; included in recovery package. |
| Entire earlier partial-work ZIP, visible Lean members | 121 | 381,908 | 8,862 | Includes copies/drafts/history; not 121 accepted proof modules. |
| New refactor resident snapshot at 20:26 EDT | 162 | 1,398,363 | 15,189 | All local `.lean` source including scripts, excludes `.lake`, `.git`, validation outputs. This is a skeleton/source inventory, not a completed proof. |

The last row decomposes as: 119 vendor files / 1,179,049 bytes / 10,501 lines; 25 Completion files / 144,996 bytes / 2,963 lines; 15 Compact files / 71,502 bytes / 1,658 lines; one 43-line adapter; one 13-line root; one 11-line script. It will change as concurrent workers finish. Exact path hashes are in `audit/refactor-source-snapshot.json`. `audit/checkpoint-source-counts.json` pins checkpoint metadata to Git tree `725f34740b0aa680c5f7f664352136fcc0528155`.

The authenticated archive scan now gives **8,732,801 lines for the historical reduction plus seven accepted exclusions**, before the unfinished-case sources. The proof is incomplete, so this is not the line count of a completed global proof. Exact per-file counts and hashes are in `ARCHIVE_LINE_COUNTS.json` and `archive-lean-source-counts.tsv`. There is not yet a measured certificate-size bound proving that the completed refactor fits 300,000 or one million lines. The early 15,189-line refactor snapshot omits unfinished obligations and giant old proofs; its size is not itself proof compression of those obligations. Replacing a large proof by an unfilled field, externalizing the same old data, or packing huge certificate literals onto one line would not meet the user's efficiency goal.

A credible global budget still needs a faithful compact instance for a genuinely costly historical case/reduction component, actual certificate byte counts and checking cost, and a count of remaining distinct supports/actions after symbolic shortening. Generic soundness alone cannot bound these. The module cap was stated as a proxy for compilation time; compiled dependencies, certificate bytes, peak memory and total checking time must be reported separately. This source inventory is not an exact live disk-usage audit and makes no claim about all pre-existing disk contents.

## 7. Evidence map and assembly order

Use `audit/BRANCHES.md`, `branch-heads.json` and `branch-comparison.json` for all nineteen branch heads, subtree equivalence and source provenance. The separate modern Lean 4.34 normalization branch (`44f32f60ebfbdf7ae7fa932da369dcb5f81fa49b`) has checked normalization source but no new case exclusions and requires an explicit model/toolchain bridge. The general Squares refactor branch is an ancestor of main, not missing independent n=12 progress.

Inherited receipts are preserved under `evidence/inherited/evidence/Baseline/foundation-replay.json`, `evidence/inherited/evidence/C{701,713,717,898,973,978,979}/case-replay.json`, and `evidence/inherited/evidence/C977/case-replay.json`. The helper receipt is under `evidence/inherited/continuation/evidence/continuation-helper-replay.json`. Per-case new findings are in `audit/C977.md`, `audit/C981.md`, `audit/C696-TERMINAL.md`; compression limits are in `audit/LEGACY_COMPRESSION.md`; earlier symbolic material is in `audit/LOCAL_RESEARCH.md`.

The safe completion order is: preserve exact definitions/foundations; finish compact generic geometric/certificate rules and their original-model bridges; close one whole substantive case with a measured compact instance; rebuild the large baseline and seven successes using that representation or shorter symbolic arguments; finish all remaining case entrances/coverage/contradictions; fill the unconditional assembly; replay the entire source closure and audit final axioms. Work that supplies a local rule or a smaller interface should be reported as such until it closes an actual whole obligation.

At this snapshot, `.verification/latest-replay.json` says `complete: false` and `global_optimality_proved: false`; its source-hashed successes are narrow module checks performed by the root worker. Later successful receipts may supersede that snapshot, but cannot by themselves fill the case obligations listed here unless their exact exported conclusions do so.
