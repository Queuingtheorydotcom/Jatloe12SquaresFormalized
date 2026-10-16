# All-branch n=12 audit — 10–11 October 2026

## Latest remote refresh — 11 October 2026, 04:59 UTC

The fresh GitHub listing contains **22 branches**. Relative to the preceding
20-branch refresh, only `main` moved, and `fix/lean-warnings` and
`refactor/unified-lean-build` were added. Every n=12 worker, integration,
normalization, ledger and recovery head is unchanged. This refresh adds **no
new n=12 exclusion, coverage theorem, or normalization result** to the earlier
mathematical inventory.

The main/fix comparison responses each stop at GitHub's 300-file display
limit. They therefore cannot justify a claim that all their edits concern
n=11. The complete Git tree checks provide the narrower, decisive evidence:

- `Lean/Proofs/N12` has tree
  `2bd9f99930d18715b2a821ec2e16ce6091801099` at preceding main
  `1a6d67e01b99f900fb8c7f2ff7994c9d60eb7828`, current main, and
  `fix/lean-warnings`. Its entire source content is unchanged.
- Current main and `fix/lean-warnings` share the complete `Lean` tree
  `3446ca0fbf6c896aa4bd2b51edb7d1e5c77cec4a`; their divergent commit
  histories do not represent independent Lean proof progress.
- The complete `Lean/Squares` trees before/after are
  `bce17d588762f74b0d190daed88815207da8d3bd` and
  `43bd12e6d3ab6846648c927c1b279dcb1b91d17a`. Both recursive tree
  responses are untruncated and contain 135 files: **34 modified, 101
  unchanged, none added or deleted**. All 68 old/new changed blobs were read.
  Every change is proof-script or API maintenance: renamed deprecated
  Mathlib imports/lemmas/tactics, removal of unused simp/tactic steps,
  `letI` to `let`, or unused binder names prefixed with `_`. No theorem or
  checker is added, strengthened, or supplied with a missing mathematical
  argument. In particular, the changes to separation, wall strips,
  half-angle bounds, pose checking and owned-hull convexity do not add a
  reusable n=12 lemma beyond the previously audited library.
- `refactor/unified-lean-build` is four commits ahead of current main. Its
  complete 16-file comparison contains workflow/build configuration,
  verification scripts/tests and documentation. The only changed `.lean`
  file is `lakefile.lean`, which is build configuration; no proof source
  changes. Potential build-tool convenience is separate from proof progress.

| Current branch | Pinned head | Refresh disposition |
|---|---|---|
| `codex/complete-twelve-squares` | `c5c6144349a1` | Unchanged; source-only n=12 checkpoint. |
| `codex/fix-canonical-axiom-reports` | `1bf942a7af1e` | Unchanged; inherited n=11 axiom-report maintenance. |
| `codex/global-uniqueness` | `47749e8dcda1` | Unchanged; inherited n=11 uniqueness work. |
| `codex/native-numerical-certificates-20261004` | `de8bbbdfd5b3` | Unchanged; older n=11 certificates. |
| `feat/n11-comparator` | `60c9d0709fb7` | Unchanged since the preceding refresh; n=11 comparison tooling. |
| `fix/lean-warnings` | `19e1e93dfc15` | Newly listed; warning/API cleanup. Its complete Lean tree equals current main. |
| `main` | `ad624c40207c` | Changed; n=12 subtree unchanged, shared-library changes are maintenance only. |
| `n12-coordination` | `730e829b6dd7` | Unchanged; modern-scaffold ledger only. |
| `n12/c1089-app-draft-20261009` | `f1d927c914bb` | Unchanged; unreplayed original-case draft. |
| `n12/formalize-normalization` | `44f32f60ebfb` | Unchanged; separate modern-model normalization lemma. |
| `n12/lean-4.19` | `e122bc2b9329` | Unchanged; original integration and seven scoped receipts. |
| `n12/ledger-4.19` | `2f2dad9fa6e8` | Unchanged; original-project ledger only. |
| `n12/worker-ben-c696-row-20261010` | `efa9c88582b9` | Unchanged; row-contract draft, no geometric exclusion. |
| `n12/worker-ben-c1090-route-preservation-20261010` | `80220fca8a8c` | Unchanged; preserved C1090 source/evidence. |
| `n12/worker-ben-codex-20261008` | `672f72ef1761` | Unchanged; seven integrated exclusions and C1090 work. |
| `n12/worker-codex-898-20261008` | `af965a97a388` | Unchanged; superseded C898 draft. |
| `n12/worker-codex-976-20261009` | `e521280b37b3` | Unchanged; all-eleven archived source, unreplayed. |
| `n12/worker-codex-c977-20261010` | `cbe674ec3998` | Unchanged; scoped reduction, residual contexts still needed. |
| `recovery/n12-lean-september-2026` | `98ddf88a36d0` | Unchanged; immutable original source provenance. |
| `refactor/squares-library` | `04a6f6b9cb91` | Unchanged; library factoring already inherited by main. |
| `refactor/unified-lean-build` | `140df8c4c7b0` | Newly listed; 16 build/workflow/tool/documentation changes, no proof source. |
| `style/comparator-lean` | `e2f3d563ad63` | Unchanged since preceding refresh; no independent n=12 progress. |

Primary evidence is saved in `branch-heads-2026-10-11.json`,
`branch-comparisons-2026-10-11.json`, `branch-tree-refresh-2026-10-11.json`,
`branch-library-sources-2026-10-11.json` and
`branch-library-review-2026-10-11.json`. The last two record every reviewed
library blob and exact maintenance patch. Remote source links are pinned to
[current main](https://github.com/EvolvingPrograms/SquaresLean/tree/ad624c40207c6386d9d74f57bde7130691de3362/Lean/Squares),
[the unchanged n=12 scaffold](https://github.com/EvolvingPrograms/SquaresLean/tree/ad624c40207c6386d9d74f57bde7130691de3362/Lean/Proofs/N12), and
[the unified-build comparison](https://github.com/EvolvingPrograms/SquaresLean/compare/ad624c40207c6386d9d74f57bde7130691de3362...140df8c4c7b00bb18c1abf6a80084796f5eda774).
No new compiler run or theorem acceptance is claimed by this source audit.
The older snapshots and branch-specific mathematical inventory below remain
historical evidence; current metadata in this section supersedes their
branch counts, head hashes and references to the then-current main.

## Earlier 20-branch remote refresh

The later GitHub refresh returned **20 branches**. All n=12 branch heads and
the recovery head remain exactly those audited below. `main` moved to
`1a6d67e01b99f900fb8c7f2ff7994c9d60eb7828` and `feat/n11-comparator` moved to
`60c9d0709fb72fabfdb4a88e6d7c6619e1fdb49d`. Their complete comparison lists
only n=11 comparison, workflow, documentation and verification-tool changes;
no n=12 proof source changed. The added `style/comparator-lean` branch at
`e2f3d563ad63cc2280b542f80437cdfdd63e9458` is one commit behind refreshed
main with no ahead commits. It adds no independent n=12 progress.
`branch-heads-refresh.json` and `branch-comparison-refresh.json` record the
responses. The table below is the earlier pinned snapshot; these three
head/branch updates supersede its corresponding metadata, without changing
its n=12 mathematical inventory.

The initial audit read the 19 then-current remote branches, their Git tree metadata, source interfaces and existing verification receipts. It does not run Lean, restore proof archives, modify a source branch, or accept any new theorem. User ZIPs are audited separately. Inherited `Lean.ofReduceBool` compiler trust is present in original Jatloe numerical certificates; a successful scoped receipt is not a completed global proof.

## Two corrections to the earlier whole-repository report

1. The latest C976 worker branch has **source assembly for all eleven residuals**, not only six. The six-residual description applied to the separate compact attempt in `codex/complete-twelve-squares`. The worker's source is mostly inside archives, so counting visible `.lean` paths misses it.
2. Those eleven archived C976 residuals contain **166,074 Lean modules and 7,009,904,025 source bytes**. The current branch `Proof.lean` imports that route. It is uncompiled, and unsuitable for the new efficiency target. The manifest counts are exact; archive payloads were not downloaded or expanded. Also, the seven already replayed exclusions have a **2,119,721,626-byte historical source dependency union**. Their tiny wrapper files do not make their complete proofs small.

Supporting machine-readable audit files are `branch-heads.json`, `branch-comparison.json`, `replay-closure-sizes.json`, and `c976-archive-inventory.json` in this directory. Source hashes in receipts were mapped to the pinned source manifest for closure sizes. No build-result hashes were newly certified by this audit.

## Initial pinned 19-branch inventory

All 19 returned branches fit on the first 100-entry API page. The status below is about proof content, not branch naming. Head hashes are pinned in the audit JSON.

| Branch | Head | Relevant contribution and disposition |
|---|---|---|
| `codex/complete-twelve-squares` | `c5c6144349` | Large source-only checkpoint for C696, C709, C974, compact C976, old C977, C981, C983, C1089, C1091 and C1092; includes integration's seven receipts. Not a completed proof. |
| `n12/lean-4.19` | `e122bc2b93` | Authoritative source integration: original geometry/foundations and seven replayed exclusions. New completion project tree `8fe3fa7ea1d28b68d22f4bfc513bed315926e1af`. |
| `n12/worker-ben-codex-20261008` | `672f72ef17` | Integration-equivalent seven exclusions plus preserved C1090 work. All its source changes outside integration are in C1090. |
| `n12/worker-ben-c1090-route-preservation-20261010` | `80220fca8a` | Same Lean sources as preceding branch; adds 1,825 evidence/proposal files under C1090. Preserve this fuller provenance, not both duplicate Lean trees. |
| `n12/worker-ben-c696-row-20261010` | `efa9c88582` | One unreplayed row-identity/nonvacuity/family-contract draft and source-review handoff. No geometric exclusion. |
| `n12/worker-codex-976-20261009` | `e521280b37` | Complete eleven-residual source assembly in compressed archives, whole-case wrapper, original trace and generator provenance. **No full Lean replay**. Most valuable as authenticated source material for a new compact certificate route. |
| `n12/worker-codex-c977-20261010` | `cbe674ec39` | New small C977 reduction, thirteen Lean files / 88,854 source bytes. Successful focused 76-module replay; still conditional on exclusions of 912 contexts. New user ZIP may extend it. |
| `n12/c1089-app-draft-20261009` | `f1d927c914` | Two source files: row contract and bridge to saved `S12.case1089_shared_impossible`. Uncompiled. Preserve both files: the large checkpoint has only the wrapper, not its row module. |
| `n12/worker-codex-898-20261008` | `af965a97a3` | Earlier C898 draft and interrupted replay. Superseded by the seven-case integration; no new whole-case result. |
| `n12/formalize-normalization` | `44f32f60eb` | Separate Lean 4.34 scaffold's completed normalization theorem. Focused four-module and 72-module scaffold checks reported, standard axioms only. Useful lemma/proof; not an exclusion and not directly the original 4.19 model. |
| `recovery/n12-lean-september-2026` | `98ddf88a36` | Immutable original source provenance. Its `Lean/Proofs/N12` subtree is identical to main's original scaffold. Do not count it as new exclusions. |
| `main` | `b0be668605` | Original modern scaffold, general Squares library, completed n=11 material; no original-project completion subtree. No unconditional n=12 theorem. |
| `feat/n11-comparator` | `eadfddf84f` | One commit beyond main; its entire `Lean/Proofs` subtree is identical to main. Adds n=11 comparison machinery, no new n=12 proof. |
| `refactor/squares-library` | `04a6f6b9cb` | Ancestor of main (12 commits behind). General geometric/checker factoring already inherited by main. Its `Lean/Proofs` has N11/N17 but no N12 subtree. |
| `codex/global-uniqueness` | `47749e8dcd` | Ancestor of main (202 commits behind), n=11 uniqueness work. No newer n=12 contribution to import. |
| `codex/fix-canonical-axiom-reports` | `1bf942a7af` | Ancestor of main (203 commits behind), axiom-report fixes inherited by main. No newer n=12 proof. |
| `codex/native-numerical-certificates-20261004` | `de8bbbdfd5` | Ancestor of main (211 commits behind), older n=11 native-certificate work. Not permission to add native checks to new n=12 geometry. |
| `n12-coordination` | `730e829b6d` | Ledger only for modern scaffold. No proof source. |
| `n12/ledger-4.19` | `2f2dad9fa6` | Ledger only for original project. No proof source. Current audit does not alter reservations. |

At the initial pinned snapshot, all original-project branches had the **same** modern top-level `Lean` tree as the then-current main (`16a0a4ccd8afc44e328beef27ff528760565f222`); differences are in the separate project. This prevents double-counting the scaffold/library as independent progress on each worker branch. A GitHub comparison establishes ancestry for the four old non-n12 branches above; metadata responses' 300-file display limit does not affect the ancestry result.

## What is actually proved, and the dependency cost

The original project's successful 63-module foundational receipt checks:

- `S12.packingConstant12_le_four`: the side-four construction.
- `S12.packingConstant12_eq_four_of_exclusion`: a conditional final assembly theorem.
- `S12.unit_packing_reduction_to_117`: arbitrary actual smaller packings reduce to the complete 117-row list; no selected-angle or finite-sample premise.

The foundation contains 62 historical modules plus `Completion.Contracts`. Their exact source total is **1,105,833 bytes and 8,964 newline-counted lines**, including the 687-byte completion interface. All resident source hashes matched the foundation receipt; four absent small source blobs were read from the pinned Git tree to complete the line count. The receipt's axiom union includes `Lean.ofReduceBool`; the source audit inventories 723 historical `native_decide` sites. This is a compact and genuinely useful preservation boundary.

| Successful case receipt | Local modules | Historical dependency source bytes |
|---|---:|---:|
| C701 | 256 | 339,882,452 |
| C713 | 225 | 266,110,547 |
| C717 | 298 | 459,733,372 |
| C898 | 198 | 188,138,692 |
| C973 | 248 | 333,362,494 |
| C978 | 227 | 268,472,356 |
| C979 | 301 | 331,494,096 |
| **Unique union** | **953** | **2,119,721,626** |

The union comprises 938 historical and 15 completion modules. All seven author receipts report `SCOPED_LEAN_REPLAY_PASS` for their actual `excluded : ExcludesCase ID` declarations. Independent row-contract checks passed, but independent full geometric acceptance is not complete. These are valid recorded scoped successes under inherited compiler trust, not new checks conducted today. Their repeated data-heavy historical dependencies must be compressed mathematically/reproved for the new source budget; simply moving them to an external import would hide the cost.

The original 117-to-18 reduction has a complete source import closure of **7,496 modules / 3,734,670,747 bytes**, but no completed fresh replay of `S12.CurrentReduction`. This corpus overlaps other original closures and must not be naively added to the seven-case union. The foundational 117-case reduction is independently useful if the refactor replaces that large later reduction.

## Remaining whole-case boundaries

| Case | Best source/replay boundary | Unresolved formal obligation |
|---|---|---|
| 696 | Local source includes one assembled root and partial other root; Ben branch only row draft. | Both-root complete exclusion remains unverified/incomplete. Local C696's exact 2,496,993-line count is external to this branch-only audit. |
| 709 | Whole-case source in checkpoint. | Lean checking/repair; shorten 36-step pair and 4-transfer certificate route. |
| 974 | Complete initial source and two entrance exclusions; remaining interface names six entrances. | Those six entrance exclusions and all internal ownership coverage; all new source uncompiled. |
| 976 | Full archived source for all eleven residuals, with whole-case assembly. Compact checkpoint separately has only six residuals. | Compact faithful replacement and Lean acceptance; source completeness is not accepted correctness. |
| 977 | Focused checked reduction to 57 ownership vectors and 16 wall branches. | All resulting context contradictions; inspect new ZIP for later coverage. |
| 981 | Checkpoint source accounts for 118/221 assignments, 55 representative obligations left. | Complete remaining representative exclusions, assembly and replay; inspect new ZIP for later coverage. |
| 983 | Domains and conditional context assembly. | Produce complete context certificates and coverage. Pinned non-Lean route has 37 contexts covering 941 vectors. |
| 1089 | Full draft wrapper/row module on its worker branch. | Check original saved exclusion's dependency closure and compact if necessary; no new full receipt. |
| 1090 | Row/family focused historical receipts, proposed initial coverage and four-step prefix. | Initial/prefix full replay, later route's 531 missing dependencies or a replacement short argument, full contradiction. |
| 1091 | Domain source and generic complete-certificate interface. | Actual complete certificate; `Proof.lean` currently imports missing `C1091.Exclusion`. |
| 1092 | Local analytic/pinwheel and frame lemmas. | Full all-packing entrance, residual parents, all ownership coverage and 35-bin ancestry. |

The modern scaffold's normalization proof is a genuinely finished separate lemma, using unchanged rotations and a positive dilation/shrink. It does not fill any of the classification/case obligations above and requires an explicit semantics bridge before reuse in the original model.

## C976 archived source: exact inventory

| Non-Lean plan vector | Archived Lean modules | Source bytes |
|---:|---:|---:|
| 25 | 3,889 | 229,276,305 |
| 31 | 4,828 | 291,799,032 |
| 35 | 4,251 | 117,356,808 |
| 38 | 16,758 | 737,950,181 |
| 44 | 41,704 | 1,796,742,045 |
| 46 | 4,997 | 129,609,557 |
| 48 | 13,808 | 515,371,191 |
| 51 | 36,881 | 1,495,802,752 |
| 52 | 3,557 | 100,614,772 |
| 54 | 7,468 | 244,518,581 |
| 57 | 27,933 | 1,350,862,801 |
| **Total** | **166,074** | **7,009,904,025** |

Every manifest says `lean_compiled: false`. The eleven trace histories contain 82, 107, 215, 525, 1,301, 293, 477, 1,264, 178, 352 and 892 connected actions respectively, including all necessary closed split children. The manifest confirms source presence/size, not that the written numerical proofs elaborate. A reported helper build is not a full residual replay. The modular verifier reduces temporary extraction cost but does not reduce the logical dependency count or repeated proof data.

## Reuse and simplification implications

1. Preserve original packing definitions and the 8,964-line verified foundational closure. Treat `CurrentReduction` and the seven large exclusion closures as **legacy evidence**, not default imports into a purportedly small build. Reimplement their finite certificate portions compactly or prove a shorter 117-case classification/exclusion route.
2. The original certificate language already separates mathematical soundness from finite rational witnesses. `AxisOverlapCertificate` proves overlap from eight separating-axis inequalities; `LinearImplicationCheck` checks Farkas combinations; `BranchPackingEnclosure.oriented_sound` connects branch points to actual normalized packings. These are reusable semantics, not a need for one bespoke theorem per numerical cell.
3. The new compact attempt already has shared pair/wall/refresh/tagged-state checker theorems. `CompactPair.Action.Check` quantifies over **every source pose**, rejects absent plans, and checks **every family block**; its soundness preserves real square coverage. `CompactTagged.run_sound` checks a sequence with state coverage. Reuse these completeness conditions while replacing repeated entire before/after lists with indexed shared data and local state updates. Reusing unchecked drafts still requires validation.
4. The seven successful exclusions and unreplayed 117-to-18 reduction are essential efficiency work, not solved small imports. This audit disproves a budget estimate based only on visible completion modules. A future budget must count the transitive `.lean`/certificate closure, uncompressed data bytes, peak checking memory and actual serial check time; newline formatting alone cannot guarantee efficiency.
5. Source-first symbolic shortening should target propagation histories and repeated Farkas/angle enclosures before producing Lean data. A general sound replay theorem can remove thousands of structurally repeated theorem wrappers, but does not automatically reduce the number or arithmetic cost of witnesses. Global validation still needs initial all-angle coverage, all split children/ties, all ownership choices, a checked terminal contradiction, and final assembly.
6. A sub-million-line completion prediction is not yet justified merely by this audit. The archived C976 route and the 2.12 GB seven-case closure are the main measured counterexamples. A representative hardest-case compact certificate and measured verifier cost are needed before promising that cap. Preserve the original theorem while exposing any unfilled obligation honestly.

## Primary evidence

- [Foundations and 117-case reduction](https://github.com/EvolvingPrograms/SquaresLean/blob/e122bc2b9329da8057ca208343436a380ab97c59/projects/n12-jatloe419/evidence/Baseline/FOUNDATIONS.md)
- [Foundation replay receipt](https://github.com/EvolvingPrograms/SquaresLean/blob/e122bc2b9329da8057ca208343436a380ab97c59/projects/n12-jatloe419/evidence/Baseline/foundation-replay.json)
- [Seven-case integration review](https://github.com/EvolvingPrograms/SquaresLean/blob/e122bc2b9329da8057ca208343436a380ab97c59/projects/n12-jatloe419/evidence/Baseline/BRANCH_SURVEY_2026-10-09.md)
- [C976 actual full-source README](https://github.com/EvolvingPrograms/SquaresLean/blob/e521280b37b39610d830a421d83f29b3702009ae/projects/n12-jatloe419/Completion/Cases/C976/README.md)
- [C976 source assembly receipt](https://github.com/EvolvingPrograms/SquaresLean/blob/e521280b37b39610d830a421d83f29b3702009ae/projects/n12-jatloe419/evidence/C976/source-assembly.json)
- [C976 all-eleven wrapper](https://github.com/EvolvingPrograms/SquaresLean/blob/e521280b37b39610d830a421d83f29b3702009ae/projects/n12-jatloe419/Completion/Cases/C976/Proof.lean)
- [C1090 preservation boundary](https://github.com/EvolvingPrograms/SquaresLean/blob/80220fca8a8ca90f4df2c3aea8cf7468dc1285cb/projects/n12-jatloe419/Completion/Cases/C1090/README.md)
- [Modern normalization handoff](https://github.com/EvolvingPrograms/SquaresLean/blob/44f32f60ebfbdf7ae7fa932da369dcb5f81fa49b/Lean/Proofs/N12/Work/N12_NORMALIZATION/HANDOFF.md)

No fresh whole-theorem replay, source generation, archive extraction, network write, or source-branch mutation was performed for this audit.
