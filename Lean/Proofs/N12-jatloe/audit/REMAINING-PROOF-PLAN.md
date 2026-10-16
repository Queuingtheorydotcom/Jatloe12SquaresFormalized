> Publication checkpoint, 11 October 2026: **86 whole original-case source terms,
> 31 pending original case contracts**, 42 pending C981 vectors, and four
> open whole-packing C1092 sectors. Whole original C977 is now source-complete,
> with independent mathematical reviews and no Lean replay of the new source.
> Read [the current checkpoint](../handoff/CHECKPOINT.md) and
> [the remaining mathematics](../handoff/MATHEMATICS-HANDOFF.md) first.
> The body below preserves an older audit; its counts and acceptance records
> describe that earlier snapshot, not the current whole proof.

# Remaining proof plan and honest size limits

> **Historical gap catalogue.** Current assembly and size status are in [ENTIRE-FORMALIZATION-STATUS.md](ENTIRE-FORMALIZATION-STATUS.md) and [REMAINING-SIZE-OBLIGATIONS.md](REMAINING-SIZE-OBLIGATIONS.md). The 58 accepted exclusions and 59 remaining original contracts are unchanged. The preferred 28-root census is 306,487 lines before the newest small additions. The compact preservation graphs still require their 64 entrances and 134 stages: original proofs exist, but these typed fields are unfinished translations. Treat older source totals and proposed allowances below as dated evidence, not a completed sub-300k deliverable or a final sub-million guarantee.

Source audit dated 11 October 2026. This audit ran no Lean, geometric search,
certificate generation, or archive recovery. It inspected the assembly
contracts, the current case interfaces, the compact checkers, and the latest
recovered-source inventory. Source completeness, historical acceptance, and
fresh Lean acceptance are different statuses throughout this document.

**The current route has 58 accepted original whole-case exclusions,
and exactly 59 other original case contracts to supply.** The final
theorem is still conditional. The older selected source union described here
was below300,000 lines; that is not the full current retained delivery. A
complete sub-million-line proof is not yet bounded by
the evidence. In particular, preserving all seven historical exclusions
within the 300,000-line assembly target remains a substantial open efficiency
problem.

## 1. Use the proof-bearing 117-case route

The authoritative new boundary is:

```lean
N12Compact.SymbolicRegistry.Pending :=
  ∀ id ∈ N12Compact.SymbolicRegistry.pendingIds,
    S12Completion.ExcludesCase id

N12Compact.SymbolicRegistry.optimality
  (remainingExclusions : Pending) : S12.packingConstant12 = 4
```

`ExcludesCase id` retains every original retained row carrying that ID and
every actual `NormalizedPacking` with its marker family. It is not a claim
about a sampled orientation, one ownership assignment, one saved polygon,
or one branch. `Remaining117.ProvenCase` stores an actual `ExcludesCase`
proof; only these proof-bearing entries remove IDs from the backlog.

The six imported groups contain 15+11+9+13+2+8 distinct whole-case proof
terms. The registry contains explicit kernel-checkable identities proving
58 known IDs, 59 pending IDs, disjointness, and union equal to the original
117. The parent has now accepted every case/group dependency and the registry
root (6.588 seconds; source SHA-256
`7b6c2a2c7eedb7f0fec87047af6c28e030dad30ad71170a630332d8068862c27`).
The final log is `.verification/Compact.Assembly.SymbolicRegistry.log`;
the inherited `Lean.ofReduceBool` dependency remains explicit. This audit
performed no compiler run itself.

`Frontier.Reduction`, `CaseSlots.HistoricalExclusions`, and
`CaseSlots.RemainingExclusions` are an alternative conditional route. They
do **not** prove the large historical reduction from 117 to 18. Do not
silently use that reduction or double-count its cost. The preferred registry
route uses the original 117-case classification directly, so completing the
59 displayed contracts is sufficient and no separate 117-to-18 theorem is
needed. `Remaining117.candidateIds` is an old proposal list and has no effect
on this proof-bearing backlog.

The original normalization, side-four construction, arbitrary orientations,
strict interior disjointness, and allowed boundary contacts are unchanged.
The reused original classification and local-query sources retain their
historical native-certificate trust boundary. Final acceptance must include
the actual final theorem's axiom report; new kernel checks do not erase
inherited `Lean.ofReduceBool` dependencies.

## 2. Exact remaining obligations

The following groups are disjoint and total 59. Their categorization comes
from the original-route inventory; it is not a claim that a compact
certificate already exists for every member.

### Twenty remaining capacity-route cases

`71,80,589,590,684,698,702,849,851,882,888,889,890,893,1075,1077,1078,1081,1083,1084`.

Each still needs an original-owner entrance, complete continuous coverage
of the needed owner poses, sound deductions sufficient to reach the stated
section-capacity terminal, and the terminal contradiction. The common
`SectionCapacity` lemmas discharge only the last implication once actual
sections have been proved. Archived final polygons and pair-operation
selectors do not discharge the preceding implications.

Two concrete shared-mathematics targets have been identified:

* In `71,80,589,590`, a merged lower central pair changes the geometry. Use
  the D4 images of `CentralPairPoint` with actual ownership to derive new
  compulsory points, then prove the remaining coupled wall/corner result.
  No complete shared contradiction has yet been supplied.
* In `849,851`, the B owner has mask34816 and actually owns the top marker
  excluded by the existing four-square theorem. A new interaction with the
  top-right singleton is needed. Relabeling the existing theorem is invalid.

For the other fourteen IDs, no shorter whole-case symbolic route is
established in the inspected sources. A compact faithful replay remains
an option; first determine and count its actual necessary witnesses.

### Twenty-one other baseline cases

`48,84,573,574,580,581,683,697,699,700,705,715,716,867,868,896,972,975,982,997,1072`.

Their missing interface is again the full `ExcludesCase id`, either through
a new symbolic argument or a complete compact replacement of the historical
route. The old reduction's source is evidence of a route, not a term in the
new registry. `715`, `982`, and `997` have explicit branch-specific routes;
all original branches and split ties must be covered.

The merged right central owner in `48,573,574` owns a marker that the current
A theorem requires missing. `CentralPairPoint` supplies a useful new
directional point, but the current four-square theorem cannot be applied
unchanged. For the other eighteen IDs, the inspected compact assembly has
no complete new replacement. This is an explicit work boundary, not a
license to assume a final enclosure.

### Seven historically accepted late cases

| Original case | Current compact status | What is still needed |
|---|---|---|
| 898 | Complete unconditional whole-case source at `Compact/Cases/C898/Complete.lean`; original direct entrance, 704 angle roots, 13 pair steps, two chord steps, final empty owner and row contract are assembled. The old initial forests/1,121 incoming leaf links are superseded. | Full bounded replay and any resulting repairs. No deliberately unfilled mathematical hypothesis remains in this source. Register its `excludes_case` only after acceptance. |
| 701 | Authenticated historical whole-case proof; compact exclusion not assembled. Original trace has 31 steps. | Convert its necessary closure or derive a complete symbolic substitute. Merged right central pair now has a short forced-point lemma; that point alone is not an exclusion. |
| 713 | Authenticated historical proof; ten-step trace is the smallest of the other six. | Best next complete preservation pilot: derive the left central forced point, then preserve or replace its actual corner/wall and central coupling. No new whole contradiction is established. |
| 717 | Authenticated historical proof; 19-step trace. | Handle the distinct upper and lower merged central bars and all retained transitions. Two forced midpoint points do not themselves finish it. |
| 973 | Authenticated historical proof; 28-step trace. | Preserve actual auxiliary alternatives and continuous coverage; the common entrance has no ready four-square triangle. |
| 978 | Authenticated historical proof; 16-step trace. | Its central owner also owns top marker15; preserve that different premise set rather than applying a missing-marker template. |
| 979 | Authenticated historical proof; 30-step trace. | Cover the upper central bar and original top-wall alternatives, with all branches retained. |

All seven original source closures are now locally authenticated. Missing
numerical downloads are therefore **not** a current blocker to inventorying
or translating these seven. Historical receipts remain meaningful evidence
of completed mathematics, but do not establish acceptance or size of the
new representation. The step counts include non-pair operations; they are
not counts of constant-size witnesses.

### Eleven other late cases

| Case | Exact compact mathematical or preservation boundary |
|---|---|
| 696 | Close both actual roots. For root one, prove a valid entrance to the coarse transfer bounds and the needed coupled owner10 chord inequality `98X + 49(C+S-2CS) - 347 ≥ 0`. Independent saved boxes, owner7/owner10 disjointness, and the proposed owner7 capacity cut are insufficient: exact counterexamples are recorded in `C696-TERMINAL.md`. A retained prefix or stronger joint argument is necessary. Existing four-wall center signs already hold and are not new progress on this gap. |
| 709 | Preserve and check the source-complete proposed entrance, 36 pair operations, and four strict border transfers, or shorten them with a valid original-premise proof. Transfer lemmas alone do not establish their entrance. |
| 974 | Preserve ownership/entrance coverage and close the six still-missing entrance exclusions; two written entrance exclusions are not the whole family. The generic three-square terminal can be reused only after its angle/center/follower premises are established. |
| 976 | Replace the source-complete but unaccepted eleven-residual archive, and preserve the reduction from 98 auxiliary vectors to those eleven. The archived route has 166,074 modules/7,009,904,025 bytes and must not enter the default build. All eleven literal residuals satisfy the new left/bottom center-cut premises, but those cuts close none of the residuals by themselves. |
| 977 | The new `C977WallCenters.excludes_case_of_four_wall_contexts` asks for contradictions for 57 actual ownership vectors in four remaining wall branches: 228 contexts. It retains the original packing, allowed transpose, strengthened missing corner, canonical bounds, and exact vector. Twelve wall branches are uniformly ruled out; no entire vector is thereby excluded. Supply complete shared continuous traces or a new symbolic contradiction for the remaining contexts. The research-to-Lean vector permutation must be respected. |
| 981 | Supply actual catalogue coverage, exclusions for all formerly connected 62 representatives, and the 55 residual exclusions partitioned in `Compact/Cases/C981.lean`. V116 has a new direct compact source proof; it is one representative, not case981. `C981WallCenters` supplies two uniform center cuts for all55 residuals. The missing lower wall barrier cannot be inferred from the neighboring C triangle: an exact counterexample rules out that shortcut. Every terminal/strip/border/angle route still needs its actual entrance and complete branch coverage. |
| 983 | Prove actual-packing coverage of the proposed 37 contexts covering 941 ownership vectors, then certify each complete trace and terminal. The context-assembly interface and research route are not the missing certificates. |
| 1089 | Bind the complete row module and wrapper to the saved `case1089_shared_impossible` proof, inspect/compact its full dependency closure, and replay it. This may be predominantly a preservation task, but the wrapper has no independent proof content. |
| 1090 | Accept the actual owner/initial coverage and four-step prefix, then prove a complete continuation and terminal. The later 23-step proposal's 531 missing dependencies are not supplied by route-preservation evidence. |
| 1091 | Supply the actual complete exclusion certificate behind the generic interface. The historical draft's missing `C1091.Exclusion` import is a real gap. |
| 1092 | Prove all-packing entrance, center/frame localization, face decomposition, residual parent coverage and angle-bin ancestry. The recovered polynomial drafts target 48 of 72 face systems; the other 24, closed-endpoint sign/identity checks, and final assembly remain. Local polynomial or pinwheel lemmas cannot replace those coverage obligations. |

The 117 C981 representatives and 117 original case IDs are unrelated
indexing sets. Similarly, 228 C977 contexts are not 228 original cases. The
registry must continue to count only completed original contracts.

## 3. What the existing compact kernel can actually preserve

The main useful interfaces are already written; several generic soundness
lemmas have focused parent acceptance. They do not assert that the remaining
case data satisfy their checks.

1. `RegionTraversalOwner.Owner.oriented_sound` links the actual square's
   inside/outside points, full closed angle cover, and initial region roots
   to an exhaustive pose cover. `RegionTraversal.Program.Check` derives
   child contexts from cuts instead of serializing repeated contexts. It
   checks both branches, strict complements, valid output leaves and empty
   certificates. Use this for complete initial coverage, not just leaves.
2. `IndexedRelaxation.cover_sound` checks every source pose, its angle, and
   every target row using shared support witnesses. This preserves incoming
   links and rounded-enclosure relaxations without duplicating full proofs.
3. `PairSupport.Check` reconstructs exact nonnegative integer support
   multipliers from four row indices. The C898 pair adapter checks all
   signed separating axes and every required neighbor pose, with actual
   disjointness. All25,843 C898 records were exactly reconstructed; this is
   evidence for that finite set, not a claim about every remaining record.
4. `SparseInteger.Certificate.Check` provides a checked fallback for local
   linear consequences and emptiness. Preserve strictness and membership
   of every referenced input row. Do not force an invalid two-row basis
   merely to avoid a fallback.
5. The C898 chord-plan checker checks neighbor coverage, certified radius
   bounds, both complementary branches, and output coverage. It is an
   implementation to factor by actual need; it does not automatically
   support arbitrary compulsory-point refresh, ownership splits, or every
   operation appearing in C976/C977/C983 traces.
6. The final case adapter must compose the actual entrance, every retained
   transition and split, and final contradiction into `ExcludesCase id`.
   A replay DAG must remain well-founded. Repeated state labels or a
   numerically stabilized cycle are not a sound induction principle.

This can avoid millions of generated proof lines by sharing mathematical
soundness, primitive rows, sparse supports, angle records, and complete
subgraphs with equal semantic inputs. The remaining uncertainty is the
number of genuinely necessary objects and unsupported operations, not the
existence of one generic Farkas theorem.

## 4. Current measured source and the unresolved budget

The counts in this section record the earlier forest/traversal snapshot.
They are retained as historical evidence, not current final-route lower
bounds. Direct initial cover now replaces those forests; the newer six-case
row/pose emission and remaining exact costs are documented in
[REMAINING-SIZE-OBLIGATIONS.md](REMAINING-SIZE-OBLIGATIONS.md).

A read-only import-closure count in this audit took 0.32 seconds. It counted
local project sources, including imported `source/S12` and `Completion`,
but not pinned external Lean/Mathlib or unused provenance archives.

| Explicit source roots | Local modules | Lean lines | Source bytes |
|---|---:|---:|---:|
| `Compact.Assembly.SymbolicRegistry` |185|20,418|1,645,187|
| `Compact.Cases.C898.Complete` |268|165,094|16,047,127|
| Union of these, `C981V116`, `C977WallCenters`, `C981WallCenters` |401|177,823|16,659,574|

These are source snapshots, not replay receipts. They are a concrete small
current assembly, not an assembly of every previously accepted exclusion.
Older budget JSON files name different roots/source revisions and should
not be presented as current whole-proof totals.

The latest complete accepted-seven source inventory is materially stronger
than the older partial-numerical-byte inventory:

| Inventory item | Exact count |
|---|---:|
| Authenticated historical source lines |5,121,803|
| Distinct affine rows |230,414|
| Distinct tree syntax nodes |194,536|
| Distinct poses |42,393|
| Pair-candidate declarations |283,495|
| Distinct weighted-row lists |106,991|
| Source lines not translated by that structural pass |3,323,189|

Source: `evidence/seven-source-inventory.json`. That pass did not verify
pair reconstruction across all seven; 1,603 declarations have unsupported
schemas. The three row/node/pose categories alone total467,343 objects.
With one source record per line, that representation already exceeds300k
before pair witnesses, relaxations, chord data and semantic bindings.
This is an obstruction to that representation, **not** a mathematical lower
bound on every possible proof. Positive-scale row normalization, smaller
empty certificates, support sharing and whole-case symbolic replacements
may reduce it. Their savings must be measured before crediting them.

Merely putting many records on one line, using macro literals, or importing
an external giant generated archive does not solve the compilation problem.
Count serialized bytes, semantic records, kernel-check time and peak RSS
alongside lines. Small module counts alone are also insufficient: the
original224 repeated rational `norm_num` angle checks exceeded the memory
guard despite occupying only a few hundred lines. The parent subsequently
reported the complete64-angle production module passing in4.336 seconds
after the direct-kernel replacement, and `SharedRows` / `SharedPoses`
passing in6.536 /12.970 seconds. Those component checks do not constitute
whole C898 acceptance. The full registry has separately passed, as recorded above.

## 5. Bounded completion plan

The earlier proposed 950,000-line allocation has been retired here: it was
an arbitrary development allowance, not evidence of a final size bound.
[REMAINING-SIZE-OBLIGATIONS.md](REMAINING-SIZE-OBLIGATIONS.md) now identifies
the actual countable objects, current measurements, direct-cover applicability,
and exact missing quantities for every late case. The user's300k assembled
and sub-million final targets remain constraints, not achieved guarantees.

The new six-case data emission is143,145 lines/44modules, retaining635,162
selected pair declarations through shared data. It still lacks cached-fan,
pruning/chord, relaxation and original-entrance proof assembly. Therefore this
is concrete improvement over the old forest format, but cannot yet establish
the preservation bound. See `evidence/historical-compact-data/manifest.json`.

The evidence supports these next gates, without a completion ETA:

1. Preserve the accepted58-case registry and finish one complete compact C898
   exclusion. Fix measured proof-check costs before duplicating the format.
2. Complete the retained fan/empty-basis/pruning/chord/relaxation inventory
   on the seven recovered proofs. Count actual serialized output, fallback
   terms, semantic bindings and still-unsupported operations. If the complete
   union cannot meet the assembled-work target, derive a whole coupled
   symbolic replacement, starting with713, or prove further representation
   sharing before expanding the corpus.
3. Pursue shared original-premise arguments for the merged-central-pair
   baseline families and849/851. A valid whole family removes an enclosure
   chain; another conditional terminal does not. Retain the C981 barrier
   and C696 pair counterexamples as regression constraints on new claims.
4. For each remaining ownership-heavy case, first build a finite route map:
   original entrance, exact context cover, branch/symmetry map, accepted
   generic operations, and terminal. Backward-slice only with proved
   dependency/coverage preservation. If more than100 distinct cases remain,
   seek a uniform symbolic condition before generating per-context proofs.
5. Translate one complete route at a time under its allowance. Root controls
   bounded serial Lean replay and process cleanup; source workers do not
   launch competing compilers. Retain the total local disk cap below10GB.
   External library compilation/cache cost must be reported separately,
   because the user's module cap is a compilation-time proxy.
6. Add only accepted full `ExcludesCase` terms to the registry, regenerate
   its exact complement, and eventually supply `Pending` without remaining
   proof parameters. The final deliverable is the unconditional original
   theorem plus full import-closure replay and axiom report.

## 6. Evidence and unresolved uncertainty

Primary source interfaces: `Compact/Assembly/Remaining117.lean`,
`SymbolicRegistry.lean`, all six `FourSquare*Cases.lean` group assemblies,
`Compact/Cases/C898/Complete.lean`, `Compact/Cases/C981.lean`, and
`Compact/Bridge/C977WallCenters.lean` / `C981WallCenters.lean`.

Case evidence: `audit/BRANCHES.md`, `C696-TERMINAL.md`,
`C977-WALL-BRANCHES.md`, `C981-SYMBOLIC-ADDENDUM.md`,
`C898_COMPACT_ASSEMBLY.md`, `NEXT-SYMBOLIC-FAMILIES.md`, and
`LATE-CASES-SYMBOLIC.md`. Numeric/source evidence:
`evidence/seven-source-inventory.json`, `numeric-input-coverage.json`,
`audit/c898-all-pair-support-reconstruction.json`, and the explicit compact
sources. Older status prose is superseded where this plan identifies newer
source assemblies or the four-branch C977 reduction.

The unresolved risks are precise: full replay of written source; the true
shared certificate size of the recovered seven; missing supported replay
forms and semantic bindings; and the genuine coupled geometry/coverage
gaps listed for the remaining cases. Neither the current177,823-line source
union nor the existence of a compact local checker settles those risks.
