# Mathematics handoff: twelve squares, continuous completion

**Checkpoint: 11 October 2026.** This document is for a mathematician or
web-based mathematical agent continuing the work without the long chat
history. Paths are relative to the project directory `projects/n12-refactored` on
branch `12Refractored`, or the project root in the standalone Lean ZIP.

**Current result: 86 of the 117 original whole-case obligations have
complete source proof terms; 31 original cases remain.** C696, C84 and
now C977 are included among the 86. C981 remains one open original case,
with 42 explicit whole-vector obligations. C1092 remains one open original
case, reduced to four whole-packing symmetry sectors. The overall theorem
is still conditional. The new source has not received the final Lean
replay, so “source-complete” never means “freshly kernel-accepted.”

The user's objective is a rigorous, substantially simplified proof of
the unrestricted twelve-unit-square packing optimum, with continuous
mathematics replacing enormous generated case trees where possible. Do
not restart completed cases or report a local lemma as a whole exclusion.

## 1. Exact mathematical problem and unchanged model

The target is `S12.packingConstant12 = 4`: the infimum of square-container
side lengths admitting twelve unit squares, with arbitrary orientations
and translations and pairwise disjoint open interiors, is four. Boundary
contacts are allowed. The attaining configuration is the explicit 4-by-3
unit grid in a side-four square; it is already supplied in
`source/S12/PackingConstant.lean`.

For the lower bound the existing normalization turns any purported
container of side less than four into a `S12.NormalizedPacking`. It has
twelve actual congruent squares of common side

    1 < a <= 1001/1000

inside `[0,4]^2`, with pairwise disjoint open interiors. This upper side
cap is a proved normalization feature, not a guessed numerical enclosure.
All subsequent work must preserve that original model. There is no
restriction to grid-aligned squares or finitely many orientations.

An `OpenSquare` is represented by real numbers `c,s,u,v,a` satisfying
`c^2+s^2=1` and `a>0`. Its interior consists exactly of the points with

    u < c*x+s*y < u+a,
    v < -s*x+c*y < v+a.

Thus U and V are orthogonal band coordinates. `loU=u`, `loV=v`; `hiU`
and `hiV` in prose mean `loU+side` and `loV+side`. The named square's
physical position and all four vertices remain relevant after a support
reduction. Replacing it by independent coordinate barriers is generally
invalid.

`ClosedFrames.canonical_frame` reindexes a single physical square's bands
so that `c>0` and `|s|<=c`, retaining its entire interior and side. This is
different from reflecting the entire packing. A full packing transform
must also transport markers, auxiliary ownership, owner names, exclusions
and any distinguished missing-corner root.

For a direction `(x,y)`, let `K=x*c+y*s` and `H=-x*s+y*c`. The exact upper
support is

    upper(x,y) = K*(u+a/2)+H*(v+a/2)+(a/2)*(|K|+|H|),

and lower support has the final plus replaced by minus. These formulas
are `upper_in_bands` and `lower_in_bands` in
`Compact/Geometry/C977NegativeCorner.lean`. SAT gives a separating
direction belonging to either square's U or V axis, with either ordering.
An exhaustive argument starts with all eight directed choices. Equality
at a supporting face is legitimate because interior disjointness allows
touching. Strict contradictions usually come from `a>1` or a genuinely
strict owned point.

### The whole-case contract

The authoritative contract in `Completion/Contracts.lean` is unchanged:

```lean
def ExcludesFamily (family : Finset Nat) : Prop :=
  ∀ p : S12.NormalizedPacking,
    S12.codedMarkerFamily p = family → False

def ExcludesCase (id : Nat) : Prop :=
  ∀ r ∈ S12.retainedRows,
    r.originalId = id → ExcludesFamily r.groups
```

Consequently a final theorem must exclude **every original retained row
with that ID**, not merely one sampled pose, one auxiliary assignment,
one selected separator, or an unrelated family. `RowIdentity` and the
case adapters connect a geometric family theorem to this exact contract.

The proved original classification `packing_reduction_to_117` covers the
normalized packing by the original 117 case IDs, using actual full-packing
symmetries. The preferred assembly uses that classification directly. Do
not assume the old separate, unfinished reduction from 117 cases to a
historical list of eighteen.

## 2. Reading map and current accounting

Read these files first:

| Purpose | Authoritative source |
|---|---|
| Original geometry and normalization | `source/S12/Packing.lean`, `source/S12/Normalization.lean`, `source/S12/PackingConstant.lean` |
| Whole original-case contract | `Completion/Contracts.lean` |
| Registry semantics and 117-case assembly | `Compact/Assembly/Remaining117.lean` |
| 79 symbolic whole-case entries | `Compact/Assembly/SymbolicRegistry.lean` |
| 79 symbolic plus seven compact historical entries | `Compact/Assembly/SourceAssembly.lean` |
| C981's exact remaining 42-vector interface | `Compact/Cases/C981Compact.lean` |
| C1092's four complete sector obligations | `Compact/Cases/C1092Compact.lean`, `Compact/Bridge/C1092WallSymmetry.lean` |
| Latest complete C977 original ending | `Compact/Bridge/C977CenterClosure.lean` |

`SourceAssembly.source_count` states 86 and `pending_count` states 31.
The seven compact historical source entries are
`701,713,717,898,973,978,979`; these are **not** additional pending
mathematical cases. Their present compact representation and whole source
closure still require the final replay. Earlier historical acceptance
receipts concern the exact sources/targets recorded in those receipts.

`SourceAssembly.Pending` has three fields:

1. Whole `ExcludesCase` proofs for all pending IDs except 981 and 1092.
2. `C981Compact.Pending`, all 42 remaining whole-vector exclusions.
3. `C1092Compact.Pending`, all four actual-packing sector contradictions.

`SourceAssembly.optimality (work : Pending)` assembles the final theorem
once those fields exist. The declaration itself does not supply them.

Older audit documents contain dated 58/59, 83/34, 84/33, or 85/32 counts,
and earlier C981 residual counts. Their useful mathematics need not be
discarded, but those totals are superseded by this checkpoint and the
live proof-bearing registry. In particular, **C977 is no longer pending**;
its former `case977_cap` skeleton must not be treated as new work.

## 3. All 31 remaining original IDs, with their categories

The exact list is:

```text
48,573,574,580,581,683,700,702,705,715,716,867,868,888,889,893,
896,972,974,975,976,981,982,983,997,1072,1084,1089,1090,1091,1092
```

The following disjoint groups account for every one of them. The
“capacity” and “baseline” labels describe the inherited route inventory;
they are not assertions that a particular proposed terminal is already
reachable.

| Category | IDs | Count | Actual outstanding obligation |
|---|---|---:|---|
| Remaining capacity-route cases | 702,888,889,893,1084 | 5 | Derive the needed full original-square sections/supports and a complete capacity contradiction, or give another whole-case argument. A saved terminal polygon or pair-operation list does not prove its entrance. |
| Shared merged-right-central family | 48,573,574 | 3 | Close the genuine SW/right-pair/right-wall/neighbor cycle for each actual family. A new common 18-point entrance exists; no whole ending does. |
| Other baseline cases | 580,581,683,700,705,716,867,868,896,972,975,1072 | 12 | Supply the complete original `ExcludesCase` theorem through shared continuous geometry or faithful compact preservation. No new completed ending is recorded here. Inspect exact row families before reusing a template. |
| Baseline cases with explicit historical branching | 715,982,997 | 3 | Preserve every original branch and split tie in the final whole-case theorem. A single branch certificate is insufficient. |
| Late auxiliary/entrance case | 974 | 1 | Historical notes identify remaining entrance exclusions and ownership coverage. Reaudit the current exact entrance; the two formerly written entrances never closed the family. |
| Large source-preservation candidate | 976 | 1 | Preserve the actual reduction from its auxiliary assignments to all residuals, then close/compact the complete residual source or replace it continuously. Old center cuts alone close none of the residuals. |
| Central-vector family | 981 | 1 | Supply all 42 `C981Compact.Pending` vector proofs; details below. |
| Large context-cover candidate | 983 | 1 | Prove complete original-packing coverage and all context endings. The historical proposal has 37 contexts for 941 vectors; that proposal is not itself a formal exclusion. |
| Saved-exclusion preservation candidate | 1089 | 1 | Authenticate and supply the actual saved exclusion behind the row wrapper, compact its necessary source closure, and replay it. A family wrapper has no independent geometric content. |
| Prefix-plus-continuation case | 1090 | 1 | Retain the original owner/initial coverage and prove the complete continuation and terminal. The recorded prefix is not a whole ending. |
| Missing full exclusion behind interface | 1091 | 1 | Supply the actual complete exclusion. Historical references to an absent `C1091.Exclusion` module cannot serve as a proof. |
| Four-wall family | 1092 | 1 | Prove all four whole-packing wall-sign sectors below. |
| **Total** | | **31** | |

For 974/976/983/1089/1090/1091, the older audits are a route catalogue,
not current acceptance receipts. In particular, do not import a huge
archive silently or assume missing certificate ancestry from a status
file. Read `audit/REMAINING-PROOF-PLAN.md` for provenance while taking
the current registry, contracts and this list as the status boundary.

### Shared cases 48, 573 and 574

`Compact/Bridge/C48RightBarOwnership.lean` supplies a new original
entrance, detailed in `audit/C48-C573-C574-SYMBOLIC.md` and
`audit/HANDOFF-C1092.md`. Actual F/G budgets are F3/G2; selected ordinary
squares may own one or two F points. The merged right owner1536 may own
zero or one. Case574's bottom owner8196 retains its genuine extra F
choice; an upper-one specification would be unsound there.

Common actual points include SW256 `(2,1.74),(1.74,2)`, NW2048
`(1.74,3)`, right pair1536 `(2.26,2)`, top32768 `(2.4,3),(2.26,3)`,
left4096 `(1,2.26),(1,2.4)`, right16384 `(3,2.26),(3,2.4)`, and the
appropriate bottom owner `(2.4,1),(2.26,1)`. Original markers, all full
squares, containers and disjointness remain available. The successful
C84 reflected theorem also requires a bottom marker on its SW square;
owner256 here lacks it. The usual four-square template requires a marker
absence that owner1536 violates. Neither theorem applies unchanged.

## 4. C981: exact 42-vector boundary and immediate research tasks

C981 has its own catalogue of **117 auxiliary ownership representatives**.
These indices are unrelated to the 117 original case IDs. A completed
representative is not a completed original case. The authoritative
remaining set is `C981Compact.unfinished`, and its exact source statement
is `unfinished.length = 42`.

```lean
def Pending : Prop :=
  ∀ i : Fin 117, i.val ∈ unfinished →
    ExcludesVector (representativeVectors[i.val]!)
```

The exact current unfinished representative indices are:

```text
2,24,25,26,27,28,29,30,31,32,33,34,36,37,38,39,40,41,43,54,55,56,57,58,59,69,70,71,73,93,94,95,98,99,101,103,104,105,106,107,108,109
```

This list is also in `handoff/obligations.json`; these are vector indices,
not original case IDs.

The original domain and symmetry cover is already imported in
`Compact/Cases/C981Compact.lean`. It consumes the completed endpoint and
rotated-endpoint families, diagonal outer argument, ordinary and double
wall/elbow arguments, full-auxiliary representatives3/4, diagonal-corner
representatives5/6/42, outer-elbow representatives35/60, and116. The total
remaining set must be read from that exact union, not an older
`pendingResidualIds` list from one component. Some component lists also
happen to have length42 but have a different meaning.

The most recent focused handoffs are:

- `audit/HANDOFF-C981-POSITIVE.md`: unfinished outer-top representatives
  34/41, current genuine positive-C geometry and exact API map.
- `audit/HANDOFF-C981-NEGATIVE.md`: complementary signed continuation,
  now frozen. It explicitly records no new whole negative-C exclusion
  and no new original-vector adapter. Its surviving negative-C axis and
  steep negative-B longitudinal alternative must remain in the work.
- `audit/C981-FULL-AUX-CONTINUOUS-CLOSURE.md`: completed3/4 route and
  its sharper, nontransferable premises.
- `audit/C981-OUTER-TOP-ORDINARY-WALLS.md`: earlier34/41 details and
  explicitly unverified local feasibility candidate.

### Representative 2: short top segment

In the useful rotated chart, the escaping northeast A has the inward
points `(2,2.26),(2.26,2)` and marker `(2.35,2.35)`. The completed row3
argument uses a top square's actual strict segment from `(1.6,3)` to
`(2.26,3)`. Row2 supplies only `(1.6,3),(1.74,3)` to that owner, so the
same argument cannot be applied.

For steep A write `z=c/(1+s)`. Exact absence of `(2.26,3)` removes
`z>=13/50`; the remaining near-vertical sector has `z<13/50`. Swapping
axes does not repair the missing point: the adjacent actual wall then
has lower points `(3,1.6),(3,1.74)`, introducing a genuine extra
transverse separator. Retain the opposite central square, the upper
central square and their actual wall/corner neighbors. A complete
all-angle vector ending, not a stronger assumed top endpoint, is needed.

### Representatives 34 and 41: ordinary right wall

The chart has original coordinates `old=(new_y,4-new_x)`. Actual owners
in this chart are:

| Role | Original owner | Genuine points |
|---|---:|---|
| Escaping NE square A | 5 | `(2,2.26),(2.26,3),(2.35,2.35)` |
| NW central B | 6 | `(1.65,2.35),(1,2.26),(1,2.4)` |
| SW central C | 7 | `(1.65,1.65),(1.74,2),(2,1.74)`, actual center and crosspoints |
| Bottom wall | 8 | `(2,.914),(1.6,1),(1.74,1)` |
| Right wall R | 9 | `(3.086,2),(3,2.26),(3,2.4)` |
| Top wall T | 10 | `(2,3.086),(1.6,3),(1.74,3)` |
| Left wall L | 11 | `(.914,2),(1,1.6),(1,1.74)` |

Owner2 is the actual NE paired corner; owner3 is the NW paired corner.
Row34 has A auxiliary pattern `{8,16}` and misses `(2.26,2)`; row41 has
`{4,8,16}` and owns that point. Neither right wall owns the diagonal
point `(2.4,3)` used in the completed35/60 ending.

`OuterTopElbowFaces` supplies the real steep faces and outer arms.
For row34, exact missing `(2.26,2)` additionally gives `2c<s`.
`OuterTopElbowReach` supplies A`(2,2.5),(2.18,3)` and the actual top
point `(1.4,3)`. The weaker top point `(1.44,3)` is available in both
rows. Row41 must not inherit the row34 narrowness or stronger reaches.

`OuterTopElbowOpposite` exhausts A/C SAT; for positive C the latest
`OuterTopElbowCentralReach` removes the C-owned axis, gives `5*C.s<C.c`,
an upper-U cap and strict C`(1.3,1.9)`. The surviving A-owned support
retains a correlation between C's two band excesses and A's displacement.
It does **not** give the old full-auxiliary tiny excess `u<.001`.

Promising next step: use the true T midpoint `(1.5,3)`, C's crosspoints
and full C/B/L coupling to derive B's real upper-U cap at that midpoint.
The positive handoff records two scalar relative-angle estimates toward
that goal. Then use the actual left square and the correlated C excess;
isolated point spans or an assumed fixed core box do not close the vector.
Negative C/B signs and row41 remain explicit additional work. None of
34/41 is excluded in the registry by these reductions.

## 5. C1092: four genuine whole-packing sectors

The original family is

    {3,12,48,192,256,512,1024,2048,4096,8192,16384,32768}.

Its actual ordered owners are four corner pairs SW/SE/NE/NW, four
central singletons SW/SE/NE/NW, then left/bottom/right/top wall singletons.
The physical wall squares must remain in the argument.

`C1092WallSymmetry` transports the entire normalized packing, exact
marker codes, owner identities, central and corner owners, wall center
cuts and all48 forced wall points. A true branch bit means tangent
center coordinate at most2, false means at least2. Bit order is
left,bottom,right,top and coordinate order is y,x,y,x. Equality is
retained. The four canonical complete tasks are:

| Field in `FourBranchEndings` | Index | Branch bits |
|---|---:|---|
| `windmill` | 0 | `[true,false,false,true]` |
| `oneExceptional` | 1 | `[true,true,true,false]` |
| `adjacentPair` | 2 | `[true,false,true,false]` |
| `oppositePair` | 3 | `[true,true,false,false]` |

Each field quantifies over every original `NormalizedPacking` with the
stated family and the corresponding `WallContext`. **All four fields are
still open.** The finite classification of sixteen Boolean center-sign
patterns under D4 is not an angle discretization. Supplying the four
fields yields the entire original case through `C1092Compact.excludes_case`.

The lower local left-wall branch supplies the whole strict segment
`x=1, 1.606<=y<=1.894`; the upper branch is reflected in y=2. Other walls
use proved coordinate maps. The full context has twelve strict targets
on each of four actual walls. Central owners avoid the foreign strict
points even in their closed squares. Actual paired corners own their
inner points, and `CornerInwardPoint` supplies additional closed points
depending on the actual common side and full container walls.

Read `audit/HANDOFF-C1092.md` for exact APIs and the frozen opposite-pair
calculation. In sector3 the two wall segments next to SW both point
toward SW, with half-turn analogues at NE. A partial face argument toward
SW inward elbows is recorded, but no whole inward-elbow theorem or
sector contradiction is supplied. An individual SW-center statement
from these barriers alone has a hand-derived counterexample. Therefore
retain actual wall support, its center cut, and the other central/corner
squares before asserting a forced center.

The geometry in `ReentrantCorridor` and `C1092WindmillGap.no_wall` excludes
all orientations of a wall among specified axis-parallel blockers. Those
blocker positions have not been forced in arbitrary C1092. The existing
eight-square windmill relaxation omits the four physical walls and shows
why the 48 forced targets alone do not finish the windmill. The
axis-central-sector note adds five angle assumptions and is not a whole
windmill proof.

## 6. Completed source mechanisms worth reusing

Prefer reuse of a theorem with its complete hypotheses over reproducing
a numerical trace. The following developments replaced substantial
earlier searches with a few continuous identities.

### C977: original missing corner, NE reach, and the bottom chain

The final theorem is `C977CenterClosure.excludes : ExcludesCase 977`.
`C977SignedEscapeClosure` first closes the missing-center branch. In the
center-owned branch all-angle northeast paired-corner geometry forces
the actual right/top middle points `(3,2),(2,3)`. The full central
incoming classification then forces the southeast B to have negative
canonical sine and true upper faces. Actual stronger missing-corner
singleton points force bottom-wall reaches `(2.6,1)` for every wall sign
and `(2.86,1)` for a nonpositive wall frame.

The final O/D/B cycle retains both signs of O and D, both actual D/B
transverse selectors, both incoming A/B longitudinal selectors and all
central signs. Negative incoming directions reduce to three endpoint
directions by exact support linearity, not finite sampling. Uniform
support, floor and width identities close the remaining cases. See
`audit/C977-POSITIVE-BOTTOM-WALL.md`,
`audit/C977-NEGATIVE-BOTTOM-ENDGAME.md` and the source imports of
`C977CenterClosure`. These are complete original source arguments,
independently hand-reviewed; full Lean replay remains outstanding.

### C696 and other shared completed families

`C696OwnedWestClosure.excludes` closes the original C696 obligation via
actual center/corner normalization and next-bottom-wall coupling. Its
negative singleton argument must retain the next wall and actual paired
corner; local three- and five-square relaxations were insufficient.
`audit/C696-CENTRAL-NORMAL-FORM.md` records the original role transport.

Other registry entries use shared four-square, merged-lower, merged-top,
opposite-central-wall, and section-capacity lemmas. Before instantiating
one, compare exact positive and negative marker/auxiliary hypotheses.
A square owning an extra marker can invalidate a missing-marker theorem
even if every required positive point is available.

### General mathematical tools

- Full `CongruentSAT.faceSeparation_of_disjoint`, `ABTransverse` support
  bounds, canonical frames and exact band rewrites.
- Strict convex segments and exact foreign-point absence to select a
  band face. A strict foreign-owned point cannot be in another square's
  closure; justify the closed/strict transition through the available
  continuity/convexity lemmas.
- Actual vertex/container identities (`bottom_wall`, positive-frame
  wall bounds, `CornerInwardPoint`) to eliminate band offsets jointly.
- Unit-circle inequalities such as `c+s>=1`, `c+s<=10/7`,
  `c>=7/10`, `s<=5/7`, and exact quadratic/cubic identities. Numerical
  bounds in this list have symbolic certificates in the cited sources.
- Cone interpolation: a square's support is linear between its own
  face-normal changes. Prove two or three endpoint inequalities and an
  exact weighted identity; keep zero denominators/equality angles.
- Rational tangent/chord bounds and half-angle substitutions, only after
  the entire parameter interval and both endpoints have been proved.
- Section-capacity contradictions, only once actual occupied rows or
  full-square support barriers have been derived.

Useful generic files include `IncreasingSegmentAvoidance.lean`,
`CentralCenterCaps.lean`, `CentralOpposedCornerChain.lean`,
`PositiveBottomSupport.lean`, `NegativeBottomWallCentralAxis.lean` and
the endpoint/row and wall/elbow families consumed by C981Compact.

## 7. Invalid shortcuts already encountered

These are substantive mathematical warnings, not optional proof style.

1. **Local O/L/A data do not force the desired center or west point.**
   Exact diagnostics found three-square examples with original marker
   and auxiliary signatures; extensions with genuine wall and paired
   corner also defeated some five-square local claims. Preserve the
   omitted opposite/bottom/right owners. Evidence includes
   `positive-central-three-square-left-point-countermodel.json` and
   `positive-central-five-square-countermodel.json` under `evidence/`.
2. **A corner pair does not automatically reach `(1,2.88)`.** A genuine
   axis-aligned top-corner pair can sit arbitrarily close to y=3. The
   earlier convenient foreign top-seed premise was unavailable. C977
   was ultimately closed with genuine paired-corner coupling and the
   actual top marker; do not revive the stronger premise.
3. **A foreign segment is weaker than the foreign square.** Entire
   marker-to-auxiliary segments can avoid A while the full missing square
   is essential to the eventual contradiction. Several exact local
   relaxations demonstrate this distinction.
4. **A whole-packing coordinate swap moves the missing-corner root.**
   If O misses `(1,1)`, swapping coordinates makes the old left singleton
   the new bottom singleton; it does not prove that new bottom singleton
   misses the corner. Preserve the actual missing owner explicitly.
5. **C981 row34 is not row41.** The former misses the inner auxiliary
   point and gets the narrowness/strong top reach; the latter owns it.
   Neither has the diagonal right-wall point of35/60. The completed3/4
   tiny-excess bound is not a universal estimate for34/41.
6. **C1092's forced targets are not physical walls.** An eight-square
   relaxation with all48 targets avoided can remain feasible. Likewise
   the five-axis-square windmill subcase is not the arbitrary-angle case.
7. **A coordinate-row membership does not fix a square's entire side.**
   An axis-aligned square owning y=3 only has `loY<3`; it does not follow
   that `loY<=3-a`. Its container gives `loY<=4-a`. One exploratory
   top-wall argument with the stronger inequality was withdrawn.
8. **A recorded numerical counterexample has a scope.** Parent-verified
   exact witnesses refute only their stated relaxations. Hand candidates
   in the C981/C1092 notes are explicitly not independently verified;
   neither sort is a counterexample to the full packing theorem unless
   all twelve actual squares and all original obligations are satisfied.
9. **Finite data checks do not prove continuous exclusion.** A boolean
   ownership predicate or exhaustive auxiliary list establishes its
   stated finite coverage. It does not replace continuous source/target
   pose coverage, SAT soundness, or the terminal contradiction.
10. **A stored proof plan is not ancestry.** Saved final boxes, stabilized
    propagation cycles, proposed angle bins and polynomial certificates
    need actual-packing entrances and complete branch coverage. Local
    certificates cannot be detached from those hypotheses.

## 8. Recommended substantial independent work allocation

Give each worker a complete mathematical obligation or a substantial
independent sector, with explicit file ownership. Do not divide an
unproved guessed lemma into many small tasks before checking its actual
premises. Avoid spending another round on already completed C977.

| Priority/workstream | Concrete target | Independence and acceptance scope |
|---|---|---|
| A: C981 row34 full chain | Finish the positive-C and complementary signed C/B/L/T chains from the new genuine reaches and correlated supports. | Split by actual central sign with shared entrance ownership. Deliver a full representative34 exclusion and original-vector adapter, not only a new point or angle bound. |
| B: C981 row41 / row2 | Take row41's additional inner point as a new full-owner entrance, or row2's short-top/near-vertical residual with all neighbors retained. | These have different missing-point hypotheses; assign separate workers. Complete every sign/selector for the chosen representative. |
| C: C1092 opposite-pair | Prove `BranchEnding 3`, retaining actual adjacent wall squares/center cuts while completing the central face analysis. | The existing one-square relaxation rules out a point-only center shortcut. A whole branch is the deliverable. |
| D: C1092 remaining symmetry types | Assign windmill, one-exceptional and adjacent-pair to independent geometric workers. | Each field is an unchanged full packing. A fixed blocker lemma is useful only after its original entrance is proved. |
| E: cases48/573/574 | Exploit the shared18-point entrance and actual merged right pair/left-top/bottom coupling. | One shared theorem with three exact family adapters can remove three whole IDs. Preserve574's larger F domain. |
| F: capacity family | Inspect702/888/889/893/1084 for a shared original-support or occupied-row mechanism. | Retain actual ownership and both signs. Prove full original capacity entrances; terminal capacity alone does not count. |
| G: late compact preservation | Audit1089,1090,1091 or the source-complete976 route in isolated ownership. | Suitable for a Lean/certificate worker, but must include all initial coverage, transitions and original-case adapter. Do not add a missing source as an axiom. |

For each new whole argument, first write a mathematical premise map:
actual owner, mask, exact auxiliary set or proved domain, strict points,
foreign absences, common side, container, pair-disjointness and allowed
symmetries. Derive a full SAT cover, then eliminate offsets while keeping
the necessary coupling. Ask for a bounded exact falsification only when a
specific relaxation is suspect and the scheduler authorizes it; no broad
uncontrolled optimizer is part of the proof.

The preceding development deliberately forbade workers from running
Lean, generators, solvers, downloads or local numerical searches. The
parent scheduled any diagnostic computation. For continuation, preserve
that policy unless the human explicitly changes it. Source reads,
hand-derived mathematics and source writing do not need a compute job.

## 9. What constitutes completion

A mathematical worker should deliver:

1. The exact intended theorem in the unchanged original model, including
   its entire sign, ownership and separator cover.
2. A continuous proof with transparent endpoint/identity certificates;
   no unproved pose enclosure, invented foreign point or omitted tie.
3. An original-family adapter deriving every premise from the actual
   packing and proving the retained row identity. For C981 this includes
   the exact `ExcludesVector` statement; for C1092 it is the entire named
   `BranchEnding`.
4. A premise/coverage audit by an independent reader, recording any
   counterexample diagnostics with their exact scope and trust status.
5. Source without `sorry`, admissions or custom axioms; any remaining
   hypothesis must be visible in an explicitly conditional theorem.

Only a full `ExcludesCase id` term removes an original ID from the
registry. Only the complete catalogue or sector cover closes981 or1092.
Then the Lean worker must compile the necessary dependency closure with
the pinned toolchain, repair elaboration/tactic failures, inspect the
final declarations and run the agreed admission/axiom audit. A source
identity checked by several mathematicians is not a compiler receipt.

The inherited classification/local-query route contains historical
native-certificate trust, including `Lean.ofReduceBool` in relevant
closures. New ordinary kernel finite checks do not erase that inherited
dependency. Report the actual final theorem's axiom set and distinguish
standard logical axioms from any native-certificate dependency. Do not
claim an axiom-free or newly pure-kernel proof merely because the latest
scalar lemmas use `ring`, `linarith` or `nlinarith`.

The user also wants the proof to be compact and reproducible. Shared
mathematics should replace repeated generated records, rather than hide
them in one-line literals, macros, opaque imported archives or uncounted
binary artifacts. No final source-size or replay-resource guarantee is
asserted here. Measure the real selected dependency closure, bytes,
semantic records, elapsed replay and peak resource use in the eventual
replay handoff.

## 10. Final checkpoint and how to resume

- **Source-complete original cases:** 86, including the new whole C977
  continuous ending. The seven historical compact replacements are
  included once, not counted twice.
- **Open original cases:** the 31 listed in Section 3. C981's 42 vectors and
  C1092's four sectors refine two of those cases, not additional IDs.
- **Still unproved globally:** the remaining `SourceAssembly.Pending`
  fields and thus the unconditional unrestricted optimum in this route.
- **Still unverified by fresh replay:** the complete newly assembled
  source closure, including new whole-case and scalar modules.
- **Best starting points for new mathematical work:** the focused C981
  and C1092 handoffs plus the exact compact pending interfaces, followed
  by the shared right-pair entrance and remaining capacity cases.
- **Do not redo:** completed C696/C84/C977 local endings, or historical
  preservation already represented by actual registry terms. Revisit
  them only for a concrete source failure or a justified shared reuse.

This file was assembled from current source and worker mathematical
receipts. Writing it ran no compiler, solver, generator or numerical
calculation. The separate Lean/packaging handoff and archive manifests
should identify the frozen commit, included source roots and validation
receipts; those artifacts, rather than a guessed commit in prose, define
the reproducible publication checkpoint.
