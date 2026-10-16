> Publication checkpoint, 11 October 2026: **86 whole original-case source terms,
> 31 pending original case contracts**, 42 pending C981 vectors, and four
> open whole-packing C1092 sectors. Whole original C977 is now source-complete,
> with independent mathematical reviews and no Lean replay of the new source.
> Read [the current checkpoint](../handoff/CHECKPOINT.md) and
> [the remaining mathematics](../handoff/MATHEMATICS-HANDOFF.md) first.
> The body below preserves an older audit; its counts and acceptance records
> describe that earlier snapshot, not the current whole proof.

# Entire n=12 formalization: current compact route

Snapshot: 11 October 2026, after the complete 58-case registry replay, the
accepted full C898 chord fusion, and the exact cyclic-support audit for the
other six historical cases. **The unconditional theorem is not yet proved by
the compact project.** All 58 original exclusions in the symbolic registry
are accepted, and exactly 59 original case contracts remain. The preferred
C898 whole-case source is `CompleteCached`; its full acceptance is pending.
The original C713 progress root exposes exactly nine pair-stage contracts.
The new all-six concrete producers now supply proposed implementations for
those and the other original contracts, with a final actual-packing
composition prepared separately. This is not acceptance of those dependencies
or another completed case.

The complete virtual preferred-source census is **294,931 lines in 3,988
project modules plus two retained draft files**, totaling 21,569,633 bytes.
It includes the complete proposed six-case entrances/stages/chords, fused
contexts, box/strip bank, C898 and all independent retained roots. No unexpected
import is missing. This source overlay is not activated or fully replayed.
It is 5,069 lines below the 300k assembly target; the final sub-million bound
remains unestablished. All 83 old shared-bank modules and the generic
direct-pruning theorem passed Lean, but concrete replacement acceptance is
still required. The earlier 329,294 virtual count, 306,487 active-root count and 391,800 component
scenario describe older, different scopes. See
[PORTABLE-COMPLETION-BUDGET.md](PORTABLE-COMPLETION-BUDGET.md) and
`evidence/virtual-preferred-source-budget.json` for the current complete scope.

This is a source/status audit, not a compiler or numerical run. Parent replay
reports and saved receipts supply the validation facts below. Older audit
counts describe their dated representations; this document identifies the
important changes rather than adding incomparable snapshots together.

## The actual theorem and assembly boundary

The original target remains `S12.packingConstant12 = 4`. The existing original
foundation supplies the attaining construction, normalization and complete
117-case classification. It covers actual packings with arbitrary square
orientations and strict interior disjointness, allowing boundary contact.

`Completion/Contracts.lean` defines `ExcludesCase id` as exclusion of **every
retained row carrying that ID**, for every actual normalized packing with
that row's marker family. A local polygon, ownership vector, sign branch or
fixed angle does not satisfy this contract.

`Compact/Assembly/Remaining117.lean` starts directly from the original 117
IDs. Each `ProvenCase` contains both its ID and an actual `ExcludesCase` term.
`knownIds` is derived from these terms, and `remainingIds` is the exact
complement. The conditional assembly is:

```lean
N12Compact.SymbolicRegistry.Pending :=
  ∀ id ∈ N12Compact.SymbolicRegistry.pendingIds,
    S12Completion.ExcludesCase id

N12Compact.SymbolicRegistry.optimality
  (remainingExclusions : Pending) : S12.packingConstant12 = 4
```

The skeleton does not assume the unfinished large historical reduction from
117 cases to 18. It does not use the old `candidateIds` proposal list to
delete work. Supplying all 59 displayed contracts and checking the final
unconditional assembly suffices for this route.

Source inspection found no admission, axiom declaration or weakened case
contract in the registry or its assembly helpers. All six groups bind their
actual excluded family to an original row. `RowIdentity` proves uniqueness
using original `retainedRows_ids` and `survivors_distinct`, then checks only
the selected row's ID/family. It does not treat a family lookup as geometry.

## Preferred deliverable roots and exclusions

Use explicit root lists and their transitive imports, not a wildcard build of
every experiment in `Compact`. The intended deliverable has these layers:

| Root or source group | Purpose and current boundary |
|---|---|
| `Compact.Assembly.SymbolicRegistry` | Accepted 58 original `ExcludesCase` terms, exact 59-case complement and conditional original target. Preserve its checked source closure. |
| `Compact.Cases.C898.CompleteCached` | Preferred actual whole-C898 candidate: `RecipeInitial.Entry`, thirteen `CachedPairs` stages, `CompactRelaxation.All`, and accepted `ChordFused`. Its final public theorem takes only the original packing/family premises. Whole replay remains pending. |
| `Compact.Cases.C713.Assembly` | Preferred C713 progress root: original entrances, occupied-row replacement and exact nine `PairStages`. It proves only `family_impossible_of_pair_stages`; source assembly is not acceptance of its pending concrete imports. |
| `Compact.Preservation.C701`, `.C713`, `.C717`, `.C973`, `.C978`, `.C979` | Emitted and activated conditional graphs of the exact original active stages; replay is pending. Each `Pending` field is an actual-packing entrance or exact original source/neighbor-to-target implication. No JSON status or archive receipt is treated as a Lean proof. |
| `Compact.Bridge.C977WallCenters`, `Compact.Bridge.C981WallCenters`, `Compact.Cases.C981V116` | Separate useful progress roots. Retain them in the handoff; they do not discharge original cases977 or981 and need not be unconditional theorem imports until used by a completed route. |

The six preservation graphs must use **one complete shared bank** at
`Compact.HistoricalData`, preserving all 114,465 row IDs and 28,235 pose IDs.
`scripts/prepare_historical_union.py` emitted bounded leaf modules plus the
same public lookup API. Graph emission with `--alias-bank` verified that bank
against every original record before writing only a small alias module. The
former C713-only sparse defaults were insufficient for the other five cases.
Preserve their old source as evidence outside the final live import closure;
do not ship a second complete or semantic-only bank alongside the union.

Keep the following **outside the preferred production root union**:

* C898 `Complete`/`Mixed` and `CompleteFusedProposal`/`MixedFusedProposal` are
  alternative assemblies. Their declarations can overlap the preferred
  assembly, and compiling all alternatives is not additional proof coverage.
* The old C898 initial forests, explicit `DirectInitial` proof tables, dense
  boundary-hint tables, old pair tables and old full relaxation tables are
  fallback/source evidence. Keep original input modules still imported by the
  new recipes. In particular, do **not** delete the whole `DirectInitial`
  directory: `DirectInitial.Inputs` is a current dependency.
* Single-root pilots, `Diagnostic`, `Prefix`, benchmark and `Proposal` modules
  are development evidence unless the chosen production root actually imports
  them. `ChordFusedEmptyPilot` validates one example but is not needed by the
  accepted complete fused transition.
* Earlier explicit-support fan emissions and the standalone semantic-bank
  fallback are superseded by the all-six cyclic tables and one union bank.
  Archived `.lean.gz`, numerical JSON and old source copies are provenance,
  not hidden compiler inputs or proof terms.

Dependency-guided exclusion is essential: `ChordFusedGeometry` still imports
the small `ChordPlans` helper for shared radius/window semantics. Its name
alone is not evidence that it can be removed. Likewise, the retained 927-link
API still has consumers; the accepted fusion's 101 bypassed chord links should
be omitted only after their remaining references are removed and checked.

## Which 58 cases are assembled, and what has passed

| Source group | Original IDs | Validation boundary at this snapshot |
|---|---|---|
| FourSquareCases (15) | 28,78,537,556,565,567,569,570,575,576,577,585,1085,1086,1087 | All 15 case modules and their whole-group assembly passed parent replay. |
| FourSquareVariantCases (11) | 405,424,985,990,993,994,999,1063,1064,1069,1070 | All case modules, group and registry passed. |
| FourSquareConvexCases (9) | 445,454,862,864,992,995,998,1001,1002 | All case modules, group and registry passed. |
| FourSquareHighRightCases (13) | 678,680,691,694,711,846,847,852,853,886,887,1073,1074 | All case modules, group and registry passed. |
| FourSquareUnusedCases (2) | 841,842 | All case modules, group and registry passed. |
| FourSquareHighRightExtraCases (8) | 669,670,673,674,675,690,848,850 | All case modules, group and registry passed. |

The accepted registry proves the exact 58/59 partition of the original 117.
`Compact.Assembly.SymbolicRegistry` passed in 6.588 seconds; source SHA-256
`7b6c2a2c7eedb7f0fec87047af6c28e030dad30ad71170a630332d8068862c27`.
Its log and source-hashed checked-module closure distinguish this completed
scope from the batch's later unrelated C898 adapter failure.

The shared orientation-free `FourSquareTemplate.impossible` passed in 2.018
seconds. The revised `RowIdentity` passed in 7.939 seconds and
`FourSquareCases` in 6.085 seconds, without the prior memory-guard failure.
These are scoped checks, not an unconditional packing theorem. The original
packing/ownership adapters and row uniqueness retain historical
`Lean.ofReduceBool` dependencies. Standard-axiom geometry does not remove
that inherited trust. The final accepted target must have its own axiom
report.

Recent source repairs changed proof implementation only: direct row lookups
replaced repeated full-table scans; rational list-membership proofs under
`classical` use `norm_num`; fourteen unmatched noncomputable sections received
their missing `end`. No ownership, inequality or case premise was weakened.

Evidence: `.verification/checked-modules.json`,
`.verification/Compact.Assembly.SymbolicRegistry.log`,
`evidence/assembly-direct-row-lookups.json`,
`evidence/four-square-bridge-rational-membership.json` and
`evidence/four-square-section-end-repairs.json`.

## The exact 59 contracts outside the source registry

These four disjoint groups total 59. Every listed item requires the full
original `ExcludesCase` contract, including its original entrance and all
branches. Historical proof acceptance and compact-source acceptance remain
separate.

| Group | IDs | Remaining obligation |
|---|---|---|
| Capacity-route baseline (20) | 71,80,589,590,684,698,702,849,851,882,888,889,890,893,1075,1077,1078,1081,1083,1084 | Derive the required real sections from actual original ownership, or replace the whole chain symbolically. The shared capacity theorem proves only the terminal once those sections hold. |
| Other baseline (21) | 48,84,573,574,580,581,683,697,699,700,705,715,716,867,868,896,972,975,982,997,1072 | Supply a complete symbolic exclusion or a compact preservation of every required transition/branch. The old later reduction is not imported as an assumed shortcut. |
| Historically accepted late cases (7) | 701,713,717,898,973,978,979 | Preserve and accept the original exclusions in a small representation. C898 has a complete candidate source chain; the other six have authenticated active contracts and source-prepared concrete composition through actual entrance/stage adapters. Original receipts, finite audits and uncompiled composition source do not validate these new representations. |
| Other late cases (11) | 696,709,974,976,977,981,983,1089,1090,1091,1092 | Complete the concrete case-specific boundaries below. |

| Late case | Concrete boundary still to discharge |
|---|---|
| 696 | Both original roots. The first root still needs a valid coupled entrance to the owner10 chord bound; independent saved boxes and the proposed owner7 pair/capacity cuts have counterexamples. |
| 709 | Accept/compact the complete proposed entrance, 36 pair operations and four border transfers, or replace the whole route. A transfer lemma does not establish its entrance. |
| 974 | All ownership/entrance coverage and six still-missing entrance exclusions. The three-square theorem helps only after its actual angle, center and follower-section premises are derived. |
| 976 | Preserve the actual 98-vector reduction and exclude all eleven residuals. The 166,074-module archived source is unaccepted and cannot be used as the small build. Uniform wall cuts do not close a residual. |
| 977 | The new bridge leaves 57 actual vectors in four wall branches, 228 contexts. Prove the remaining coupled contradictions with original owner numbering and exact transpose. The 12 eliminated wall branches do not exclude any entire vector. |
| 981 | The exact `C981Pending` interface requires original catalogue coverage plus the other 116 representative exclusions, using the completed V116 proof explicitly. The former 62 connected and 55 residual labels describe the original inventory; the residual 55 alone are not the remaining case proof. `CaseVectors` coverage/transpose remains explicit. The two residual wall-center cuts close no whole representative. |
| 983 | Actual-packing coverage of the proposed 37 contexts covering 941 vectors, followed by every complete trace and terminal. Research context labels are not those certificates. |
| 1089 | Recover the whole semantic dependency binding of the saved exclusion, compact it and accept the actual row/whole-case theorem. The small wrapper has no independent geometric content. |
| 1090 | Accept actual-owner initial coverage and the prefix, then provide the complete continuation/terminal. Preserved proposals do not supply missing later dependencies. |
| 1091 | Supply the actual complete exclusion behind the generic interface; the historical missing `C1091.Exclusion` remains a genuine boundary. |
| 1092 | All-packing entrance, frame/center localization, all face systems and residual parent/angle ancestry. Draft polynomial work for 48 of 72 face systems leaves the other 24 and the global bindings open. |

The 117 C981 representative indices are not the 117 original case IDs.
Likewise, C977 contexts are not additional original cases. For complete source
interfaces and prior counterexamples see [REMAINING-PROOF-PLAN.md](REMAINING-PROOF-PLAN.md),
[C696-TERMINAL.md](C696-TERMINAL.md) and [C981.md](C981.md).

## The preservation route changed materially

### C898: actual fused theorem accepted; whole candidate still pending

`Compact/Cases/C898/CompleteCached.lean` imports `RecipeInitial.Entry` and
`MixedCached`. It avoids the old initial forest and its 1,121 incoming leaf
links. The proposed entrance reaches the identical reduced pose domains for
all 704 owner/angle roots. The chain then uses thirteen pair stages and one
accepted fusion of the former two chord stages, ending in the same empty
owner domain.

The complete `ChordFused` theorem passed in 3.097 seconds; its 53-plan data
passed in 13.741 seconds and all six neighbor-window tables in 11.562 seconds.
It maps the original 53 source poses to the original 49 target poses, proving
the four omitted angles empty. The source contains419 distinct two-row
supports. The original owner5 markers and side cap rule out one side of each
window, so both remaining strict cuts apply directly to the initial owner
domain. This bypasses 105 branch plans, 101 chord relaxation links, 101 raw
chord pieces and 52 intermediate relaxed poses. It does not omit any of the
six actual foreign-cover premises. `CompleteCached` derives the extra
internal marker/cap facts from the original packing; no new global
geometric assumption was added.

The complete original-domain terminal pair stage14 passed in 15.280 seconds.
Stage04 has 448 accepted numerical pairs and their exact raw transfer to the
old pair-check interface, but its whole domain transition still depends on
the compact relaxation/metadata replay. The other eleven pair stages are
source-assembled, not accepted complete transitions. All 704 recipe checks
and their original owner bindings, the remaining pair transitions, and the
final mixed/family/row assembly must still pass. Whole C898 remains outside
the registry. See [C898-BACKWARD-SLICE.md](C898-BACKWARD-SLICE.md).

The newer context representation passed a complete exact audit in 2.885
seconds: 858 of the 1,002 nonterminal contexts use boundary cycles; 144 retain
their exact original two-row fans because a cycle would weaken a requested
bound or its strictness. All 25,419 nonterminal pairs and 203,352 axes passed;
the accepted terminal's 424 pairs stay separate. Emission gives 9,403 lines
in 17 modules, replacing 35,799 lines. The existing `CachedPoseRecipe` helper
adds 50 lines, so the measured net component saving is 26,346 lines before
shared-core accounting. The parent is activating this proposal; its concrete
Lean checks remain pending. The fallback contexts have not been omitted.

A second reduction replaces repeated pair tests with a point forced strictly
inside both actual squares. The complete C898 finite audit covers 19,267
of 25,843 pair scopes by shared points and preserves 6,576 explicit pair
fallbacks. It checks 3,825 point memberships: 15,300 own-face inequalities,
plus 52,608 fallback axes, for 67,908 scalar comparisons rather than 206,744.
The audit passed in 9.017 seconds. The generic original-square point bridge
and the focused Step04 point/fallback checks are accepted; the complete
thirteen-stage Lean replacement and final case assembly are not thereby
proved. Its actual source closure must be counted after activation.
The current production proposal retains manual Step04 and the accepted
old terminal Step14: it uses 3,756 point checks and 7,007 pair fallbacks,
or 71,080 face/axis comparisons. These are different scopes from the fully
automatic finite audit above. The new independent terminal now passed its
original transition in 10.396 seconds, using 61 point memberships instead
of 424 pairs. The production counts above precede integrating that accepted
terminal. This still does not establish whole C898.

### Direct initial coverage: whole forests replaced by a continuous theorem

All seven historical source closures are locally authenticated. The completed
finite direct-cover audits cover 75 owner entrances and 6,848 angle roots:
312 empty/absent-target roots, 6,536 shared target poses, and 50,332
nontrivial target-row occurrences. The 3,135,744 examined boundary pairs are
checker work, not a need to serialize that many witnesses. These exact
audits are evidence for Lean checker instances, not seven accepted compact
case theorems. The accepted generic planar theorem handles full continuous
center domains, degenerate feasible sets and open forbidden rectangles.
The exact original-square bridge and rational coefficient encoder also
passed. Their finite instances still require Lean acceptance.

For C898, automatic exclusion of inactive boundary lines and unordered-pair
checks reduced 1,087,488 ordered comparisons to 124,462 active unordered
comparisons in the exact audit, preserving all 6,182 feasible vertices and
all 74 empty roots. An intermediate704-root recipe emission occupied12,487
lines; a further common-dictionary recipe representation is being checked.
That dated component count is not the current complete C898 closure.

### Six historical cases: cyclic supports and exact active graphs

Consequently the old count of 467,343 row/tree/pose records is not a lower
bound on this proposed representation: its initial forests are eliminated.
The exact all-six union is now emitted and activated:143,532 Lean lines in 83
modules, approximately9.75MB, preserving 114,465 rows and 28,235 poses under
their original IDs. Leaf modules hold at most2,048 records. This replaces
the earlier143,145-line/44-module packaging and the C713-only sparse bank;
it is one complete bank, not three simultaneous dependencies. The parent
verified all 83 generated source hashes; all83 bank modules now passed Lean.

The complete cyclic-support audit now covers639,066 required pair occurrences:
635,162 distinct selected original pair declarations plus 3,904 reused
occurrences. It checks all eight axes for each occurrence, closing21 using
one explicitly empty context and the other 639,045 by supports. Every one of
the 12,932 nonempty context fans uses an ordered boundary cycle; there are
**zero explicit-support fallbacks**. The source emission is 45,645 Lean lines
in 406 modules, superseding the earlier larger fan emission. The audit took
37.974 seconds. It is exact rational evidence, not Lean acceptance of all
context tables, axis checks, pruning outputs or complete exclusions.

The shared bank plus cyclic fans occupy 189,177 emitted lines. The six exact
graph adapters add 2,772 lines in 7 modules, giving 191,949 lines across these
three components before C898, foundations, entrances and further transition
semantics. The remaining17,651 relaxation links and 5,645 blocks are real
semantic work; their original records are not proof terms already included
in that subtotal.

The subsequent complete shared-point audit passed in 108.634 seconds under
256 MiB. It covers 412,377 occurrences geometrically, retains 226,668 exact
eight-axis fallbacks and rechecks all 21 empty-context closures. The 52,814
point memberships require 211,256 own-face inequalities; fallback axes add
1,813,344, for 2,024,600 comparisons instead of 5,112,360. All 113 original pair
stages are covered by 3,392 exact rectangular groups, with a maximum of 61 in
one stage. The selected points use 48,300 distinct own-direction supports.
No unsupported item remained. This is a completed exact audit, not emitted
and accepted Lean tables or six whole-case proofs.

The six graphs still have 64 actual entrance fields and 134 stage fields.
The original accepted proofs supply their mathematical route, but the
compact translation is incomplete. The new direct-pruning generic proof
passed Lean in 7.715 seconds with ordinary axioms. Its complete exact audit
then passed in 2.410 seconds: all 16,896 outside-block regions from all 9,166
plans directly imply an original final target. No region needs a further
split or unsupported closure. The 2,153 zero-output plans have an empty
blocked conjunction; their separately checked overlap contradiction excludes
the source, rather than silently treating missing outputs as an empty set.
All 17,651 old relaxation links also passed an independent exact hint audit.
The new route bypasses pair-only intermediate poses and links entirely, but
the concrete Lean `Plan.Check` instances and exact source/output bindings
remain required. `evidence/historical-outside-coverage` contains the complete
branch evidence. The original chord stages are retained separately.

The authenticated backward graph keeps the exact following obligations:

| Case | Original pair stages | Original chord/window stages | Exact terminal |
|---|---:|---:|---|
| 701 | 26 | 5 | `Domain3_31` empty |
| 713 | 9 | 1 | `Domain8_10` empty |
| 717 | 17 | 2 | `Domain6_19` empty |
| 973 | 23 | 5 | `Domain10_28` empty |
| 978 | 14 | 2 | `Domain11_16` empty |
| 979 | 24 | 6 | `Domain4_30` empty |

All 134 stages are terminal-relevant in the original graph. Removing a stage
because its surviving pose IDs do not occur at the terminal is unsound: its
closed branches and neighbor refinements still require proof. The semantic
domain union uses 12,078 distinct poses and 84,054 rows. It is not emitted as
another bank alongside the complete shared data. The seven graph source
hashes were verified with the union; Lean replay remains pending. Their
`Pending` fields retain actual-owner masks, original family/row identity,
entrances and exact source/neighbor/target implications. They provide honest
conditional composition, not 134 proved stages.

The complete bank-reachability audit of the original route also finished.
Retaining that route needs all 28,235 poses and 114,465 rows. Substituting the C713
height route removes only six poses and six rows, not the tens of thousands
suggested by considering semantic domain endpoints alone. No substantial
bank-pruning saving is included in the active budget. The newly audited
direct-pruning implication changes that dependency graph. Its dependency
audit passed and emitted a proposal preserving all fans, final targets and
21 original chord stages: 99,562 rows and 12,682 poses, occupying 112,997 lines
in 75 modules. This saves 30,535 emitted source lines against the full bank.
The original global IDs and dictionary API are unchanged. Activation still
requires accepting the replacement checks, retiring pair-only old consumer
imports, and replaying every importing theorem. The proposal is not a second
required bank in the final closure.

For C713, `OccupiedRow` passed in 2.126 seconds after the original ownership
entrance's 605 query and 24 domain checks passed. The three actual foreign
points at height 87/50 force the original owner7 center strictly above that
height plus its certified section radius. This replaces the historical
chord's propagated-neighbor requirements, preserving arbitrary orientations.
All 108 output records and `HeightData.All` now passed, followed by
`ChordDirect` in 5.533 seconds. This is the original actual-packing/incoming-
domain implication to `Domain7_6`, without the obsolete propagated-neighbor
premises. The 1,152 initial recipe roots and complete nine pair transitions
remain to be accepted. `Assembly` names exactly those nine `PairStages`.
It has no unconditional `ExcludesCase713` claim.
The earlier 642,781-declaration pass had incomplete bindings and is superseded
for this six-case emission scope.

See [SEVEN-DIRECT-COVER-AND-EMITTER-PLAN.md](SEVEN-DIRECT-COVER-AND-EMITTER-PLAN.md)
for the representation and exact input evidence, plus
`evidence/historical-compact-data/manifest.json`, the manifests in
`evidence/proposals/HistoricalUnion` and `HistoricalGraphs`,
`evidence/historical-fans-701-713-717-973-978-979-cycles/manifest.json`, and
`evidence/historical-active-graphs-audit.json` for the data and graph audits.
These do not yet establish a 300,000-line complete preservation bound.

## Whole-family simplifications worth completing next

No additional whole open family was proved by this audit. The following
targets share genuine original premises; their listed gaps are substantive.

| Shared target | Already available | Missing implication that would remove a whole route |
|---|---|---|
| Right central-pair cases 48,573,574; related 701 | `CentralPairPoint` and D4 give a strict outward point from the two owned central markers and the two missing opposite markers. | A joint bar/wall/corner contradiction covering every allowed auxiliary owner. The old A template is inapplicable because its supposedly missing marker is owned. |
| Lower central-pair cases 71,80,589,590; related 717 | The same all-angle lemma gives `(2,1.5)`. | A complete coupled lower-wall/neighbor contradiction, not merely another forced point. |
| Adjacent top-bar cases 849,851 | Existing A/L/R arguments give A's points at `(2,2.5)` and `(2,2.4)`, hence exclude B's long section on `y=2.4`. | Use the actual top-right singleton and B's owned top marker to prove a new joint contradiction. The old B-missing-top-marker premise is false here. |
| C713, with potential reuse in 701/717/978/979 | The complete original-owner chord replacement, including all 108 outgoing records, is accepted for arbitrary orientations. | Accept the initial covers and nine pair stages. Before reusing it elsewhere, bind actual occupied points, check each historical window endpoint and prove all outgoing target rows. A forced midpoint alone still does not imply a long section. |
| C976/C977/C981 wall-sign families | One original-point center barrier removes opposite half-space branches uniformly. | A common surviving-context contradiction. Do not emit hundreds of separate traces before trying a shared coupled inequality. |
| Seven historical initial covers | One planar direct-cover theorem can replace all old initial forests, using exact original point/angle inputs. | Full Lean instance acceptance and complete later transition data. This merges whole entrance obligations, not the seven final exclusions. |

The efficient certificate alternative is shared exact rows/poses, direct
initial coverage, cached support bases and one sound transition checker.
`CachedSupportFan` certifies each selected basis's input membership and row
identity; direction lookup still checks its cone/sign/slack conditions.
Nothing relies on an unverified hull, numerical feasibility result or hash
match as a theorem premise. Constant-size local supports do not bound the
number of required contexts; measure the retained whole semantic closure.

## Module, source and cache budget: measured scope only

The latest **preferred28-root** census is pinned in
`evidence/preferred-source-budget.json`: **306,487 lines,1,335 local modules,
20,260,576 bytes**. It includes the independent roots omitted by the older
four-root report below. All resident active/draft source in this newer
snapshot is **518,110 lines in1,681 modules**. The newly accepted direct-pruning
module and unresolved draft must still be added to the selected count.
Consequently the300k target remains exceeded; the older298,422-line result
must not be presented as the complete delivery.

The earlier scoped census resolved `Compact.Assembly.RefactorInventory`,
`Compact.Cases.C898.CompleteCached`, `Compact.Cases.C713.Assembly`, and
`Compact.HistoricalFans.C701_713_717_973_978_979.All`. It includes their full
transitive data rather than counting the wrappers:

| Current local scope | Lean lines | Modules | Bytes |
|---|---:|---:|---:|
| Those four resolved roots | 298,422 | 979 | 19,108,128 |
| All resident active and draft source | 500,326 | 1,390 | 34,594,255 |

The four-root scope omits independent C713 relaxation, `Compact`, additional
geometry/catalogue roots and the common-point candidate. The complete
expanded root manifest is `evidence/preferred-delivery-roots.json`; the newer
28-root result is above. One useful retained draft,
`adapters/C696SymmetryOriginal.lean`, has a missing original import and must
be counted separately without being presented as an accepted build root.
The first table row is therefore not a complete delivery below 300k.

An earlier read-only census resolved every dependency of the five roots
`SymbolicRegistry`, `C898.Complete`, `C977WallCenters`, `C981WallCenters` and
`C981V116`, including implicit `Init`, pinned Lean 4.19, Mathlib and package
sources. It read approximately 9.18 MB of headers and invoked no compiler.

| Dated root union above | Source modules | Source bytes | Existing `.olean` bytes |
|---|---:|---:|---:|
| Project | 360 | 14,249,936 | 176,268,008 |
| Lean/Mathlib/other packages | 2,431 | 25,761,919 | 1,642,438,720 |
| Total | **2,791** | **40,011,855** | **1,818,706,728** |

At that census, all 2,431 external objects existed, while 181 project objects
were absent. Object presence is not a freshness or acceptance certificate.
The last 1,921-module cache plan was not the full import union; it omitted two
currently imported Mathlib modules even though their objects existed.
These facts distinguish source dependency count, cache disk cost and remaining
validation. They do not estimate elapsed compile time.

That dated union met the below 9,000-module comparison, including external
dependencies. It predates `CompleteCached`, the full historical bank and
cyclic fans, so it is not the current preferred root census. **The final
proof's module and line counts remain unbounded by current evidence**, because
the missing 59 whole-case contracts can add imports and certificates.
The historical bank/fans/graphs alone now total 191,949 measured source lines,
leaving 108,051 lines for every other dependency under the 300k target. After
the emitted C898 cycle conversion, the explicitly counted C898 bulk groups
and context helper add 60,244 lines. This working subtotal is 252,193 lines,
leaving 47,807 for all omitted dependencies and semantic bindings; it is not
a full proof closure. The complete 294,931-line virtual measurement above
supersedes those component/root counts and includes all new concrete
historical source. It is 5,069 lines below the assembly target, and its
proposal dependencies still need full acceptance.
Source bytes and semantic record counts must accompany any refreshed line
count. Neither dense formatting nor excluding required certificates meets
the requested efficiency target.

The 300,000-line assembled-work target and below-one-million final target are
development constraints, not achieved global guarantees. A valid budget must
count all seven preserved exclusions, all 41 other baseline cases and all
eleven other late cases, sharing dependencies once. Prior proposed category
allowances in older budget documents are not evidence of attainability.
The current measured objects and exact missing quantities are in
[REMAINING-SIZE-OBLIGATIONS.md](REMAINING-SIZE-OBLIGATIONS.md).

Evidence: `evidence/all-import-budget.json`. The local storage cap remains
below 10 GB; this census measures only the dependency subset and is not a
fresh whole-disk usage report. Root-controlled serial replay and cleanup
remain necessary. No evidence-based final ETA is available while the complete
C898 check, retained certificate inventories and missing case mathematics
remain unfinished.

The path toward a defensible sub-million final bound is to measure the whole
preferred retained union, accept the shared-point arithmetic reduction,
then add only measured complete case increments. The six-case point auditor
preserves all 635,162 distinct declarations, their 639,066 occurrences and
21 certified empty closures; it uses at most 100 groups per each of the 113
pair stages. That bounded representation passed the complete finite audit,
but is not an accepted Lean replacement or a bound on the still missing late-case mathematics. The
unknown complete objects in C976/C977/C981 and C983/C1090–1092 remain explicit
budget risks rather than invented numeric allowances.

## Next acceptance gates

1. Preserve the accepted 58-case registry and its source/axiom receipts.
2. Finish the preferred C898 replay, retaining the accepted full fused
   transition and terminal stage14; resolve the measured initial/pair-check
   bottlenecks before broad compilation. Register only the accepted actual
   `ExcludesCase898` term.
3. Replay the one complete historical bank and exact conditional graphs;
   discharge C713's initial/output records and nine pair stages as the next
   whole case. Accept all cyclic fan and transition bindings, not just their
   source emission. Prune bank records only using the union of all live
   entrance, fan, block, relaxation, chord and graph dependencies.
4. Pursue the coupled symbolic families above where they remove full prefix
   chains. Preserve the existing C696/C981/C713 counterexamples as constraints.
5. Add only complete original exclusions, maintain the exact finite complement,
   and finally check unconditional `packingConstant12 = 4` with no pending case
   argument. Until then, the overall formalization remains unfinished.
