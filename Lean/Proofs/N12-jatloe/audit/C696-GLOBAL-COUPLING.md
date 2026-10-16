# C696: retain the full boundary cycle

11 October 2026. Source and hand mathematics only; no Lean compilation or
local search was run by this worker.

The exact five-square counterexample in
`evidence/positive-central-five-square-countermodel.json` satisfies the
original southwest O/L/A data, the full left wall square, and the full
northwest paired corner, while A misses the center. Adding the paired
corner therefore does not repair the rejected local center implication.
This is not a twelve-square packing.

## Original owner map

| Owner | Marker mask | Exact combined auxiliary indices | Role |
|---|---:|---|---|
| 0 | 1 | 2,12 | Southwest bottom singleton |
| 1 | 2 | 0,10 | Southwest left singleton |
| 2 | 12 | none | Southeast paired corner |
| 3 | 16 | 7,17 | Northeast top singleton |
| 4 | 32 | 9,19 | Northeast right singleton |
| 5 | 192 | none | Northwest paired corner |
| 6 | 256 | 4,13 | Southwest central square |
| 7 | 1024 | 5,16 | Northeast central square |
| 8 | 4096 | 1,11 | Left wall, extending upward |
| 9 | 8192 | 6,15 | Bottom wall, extending rightward |
| 10 | 16384 | 8,18 | Right wall, extending downward |
| 11 | 32768 | 3,14 | Top wall, extending leftward |

All sides are the same actual a, with 1<a<=1.001; every square is contained
in the original box, and every distinct pair has disjoint strict interiors.
`C696WallCycle.actual_auxiliary` derives the exact assignment from the
original family. Both paired corners really have empty auxiliary sets.
Neither is a source of a singleton seed at distance .12 from its corner.

`C696CentralReach.central_points` gives the genuine additional points
A6(2,1.5), A6(1.5,2), A7(2,2.5), A7(2.5,2). The four wall reaches are
W8(1,2.56), W9(2.56,1), W10(3,1.44), W11(1.44,3).

The physical half-turn permutes owners by
`[3,4,5,0,1,2,7,6,10,11,8,9]`. Thus the two omitted neighbors of the
southwest five-square configuration are not optional: its bottom wall9
and the opposite top wall11 enter the full family together.

## Four genuine blocked grid cuts

The original exact assignment supplies all these strict point triples:

| Cut | First integer position | Second | Third |
|---|---|---|---|
| x=1.74 | owner0 at y=1 | owner6 at y=2 | owner11 at y=3 |
| y=1.74 | owner1 at x=1 | owner6 at x=2 | owner10 at x=3 |
| x=2.26 | owner9 at y=1 | owner7 at y=2 | owner3 at y=3 |
| y=2.26 | owner8 at x=1 | owner7 at x=2 | owner4 at x=3 |

Every other actual square has no section longer than one on that cut.
The existing continuous section-radius theorem identifies the side of
each blocked cut from a compulsory point at least .51 away.

Write rho(q)=(|c|+|s|-2|cs|)/2. The new original-family adapter
`Compact/Bridge/C696GlobalSections.lean` proves simultaneously:

    centerX(A7)-rho(A7) > 1.74,
    centerY(A7)-rho(A7) > 1.74,
    centerX(A6)+rho(A6) < 2.26,
    centerY(A6)+rho(A6) < 2.26;

    centerX(W8)+rho(W8) < 1.74,
    centerY(W9)+rho(W9) < 1.74,
    centerX(W10)-rho(W10) > 2.26,
    centerY(W11)-rho(W11) > 2.26.

These are unconditional coupled consequences of the entire actual family.
They assume no missing-corner root, orientation, saved enclosure, or
unproved seed. The source has not been compiled. They are not a whole-case
exclusion.

## Next structural target

The actual bottom chain is owner0 / wall9 / paired corner2, coupled to
central6. Wall9 owns (2,.914), (2.26,1), (2.4,1), and (2.56,1); corner2
contains the genuine closed inward point (4-a,a). Its full square must
remain in the chain, not merely that point. The opposite chain follows
by the physical half-turn.

The old terminal analysis also identifies precisely this missing
interaction: owner0/wall9 separation is what moves the common vertical
section cut past 1.8. The present proof obtains the initial exact cut at
1.74 directly from the original family. Moving it farther requires real
pair support geometry, not replacing the family by independent center
boxes. The proposed full bottom-chain transfer has not been established.

The tentative bound lower_E(t,d)<=3d+.74t for a positive NW paired corner
was not proved: its high corner-tilt branch has a gap. No source theorem
asserts that bound, and it is not used by the new global adapter.

## Genuine-marker ordered-cycle scalar completed

The temporary final scalar assignment is now source-complete in
`Compact/Geometry/CornerWallMarkerNegativeHighBounds.lean`. For canonical
unit normals `(c,s),(d,t),(l,r)` with `s<=t<=r`, `t<=3/5`, `d>=4/5`, it
proves the actual negative-L high-angle support margin

    1+(l/c) B(c,s)+(l/c)(s l+c r)-r Y(d,t)-l X(d,t) >= 0,

where `B=1+s/c-2s-.914s^2/c` and `X,Y` are the two genuine marker
coefficients from `CornerWallMarkerLongitudinal`. No `(1,2.88)` exclusion
is used. The original-packing angle-order entrance remains separate.

The proof first replaces the O angle by the W angle using the already
proved monotonicity of `G=(B+s)/c`. The resulting response is increasing
on the whole remaining canonical L arc. Its finite-difference numerator
is bounded below by

    H = (Q^2-R^2)/2 - 3 Q R/4 + 7 R/4 - 13 Q/20,
    Q=l+d, R=r+t, x=Q-R.

The exact certificate is

    H = 7x^2/40 + (2-x)/50 + 3(4-Q^2-R^2)/8
        + (x+11/10)(R-7/5+7x/10).

Every term is nonnegative. The final linear factor follows by adding
`7l+3r>=7` and `7d+3t>=7`; squaring either inequality leaves the product
`2r(21l-20r)>=0`. At the equal-angle endpoint, the response is the
existing disk margin plus `.086t`. Root and ending independently checked
the identities by hand. No Lean run or local computation was performed.

## Full-chain obstruction still open

The five-square witness's bottom singleton has a rightmost tip just past
`x=2`, near `y=1`, so an axis-aligned bottom wall9 cannot simply be inserted.
A clockwise wall9 can move its left top away from that tip, but its right
top then interacts with both pairedSE2 and rightwall10. This is the first
concrete connection to the opposite half-turn chain. It is only a guide
to the actual support problem, not a proved angle or section transfer.
No bottom0/wall9/pairedSE2-only contradiction has been asserted.

## Exact paired boundary-chain interface

`Compact/Geometry/C696BottomChainSelectors.lean` now gives exhaustive
directed SAT reductions for the full chain

    O0 -> bottom9 -> pairedSE2 -> right10 -> rightSingleton4.

Its physical half-turn is the simultaneous original chain

    top3 -> top11 -> pairedNW5 -> left8 -> leftSingleton1.

For each canonical face frame `(c,s)`, the first edge has only forward U,
or forward V with `-s>(43/130)c`. The second has forward U, or backward V
with `s>(43/543)c`, or forward V with `-s>(43/220)c`. At the actual corner,
the third edge has forward V, or forward U with `s>(43/220)c`, or backward
U with `-s>(43/543)c`. The last edge has forward V, or forward U with
`s>(43/130)c`. Each selected axis belongs to one of its two actual squares.
The inequalities retain the full support functions and weak contact.

`Compact/Bridge/C696BoundaryChain.lean`, theorem `actual`, binds both
chains to the original family at once and preserves every chosen frame's
exact side and inside equivalence. The reaches `(2.56,1)` and `(3,1.44)`
come from `C696WallCycle.owned_points`, not an assumed query entry.

The same interface also retains the genuine opposite-central barriers.
For bottom9 in frame `(d,s)`, A6's point `(2,1.5)` gives:

    s>=0:  D.hiV <= 1.5d-2s;
    s<=0:  D.loU >= 2d+1.5s  or  D.hiV <= 1.5d-2s.

For right10 in frame `(c,s)`, A7's point `(2.5,2)` gives:

    s<=0:  R.loU >= 2.5c+2s;
    s>=0:  R.loU >= 2.5c+2s  or  R.hiV <= 2c-2.5s.

The half-turn supplies the corresponding central barriers on top11 and
left8. Thus neither paired corner nor either central square is replaced
by a guessed fixed core cutoff. The remaining task is to telescope these
true full-support relations, together with the endpoint corner coupling.
No whole-case contradiction follows from the interface alone. Source is
uncompiled; no computation, solver, or Lean run was performed here.

## Genuine inward occupied rows and wall strips

`C696GlobalSections.occupied_inner_rows` moves all four blocked rows to
the genuine crosspoint coordinates 1.5 and 2.5. The central entries are
the proved strict crosspoints. The outer entries use exact segment
interpolation between singleton seeds 1.12 and 1.74, or between the real
wall reach 1.44 and the original seed 1.74. No new point is guessed.

`wall_inner_cuts` consequently strengthens all four wall constraints to

    centerX(W8)+rho(W8) < 1.5,
    centerY(W9)+rho(W9) < 1.5,
    centerX(W10)-rho(W10) > 2.5,
    centerY(W11)-rho(W11) > 2.5.

The section-radius theorem uses the original side cap and full actual
disjointness from the three owners on each row. These cuts are still not
a whole-case contradiction.

## Entire positive-wall / owned-west sector closed

`Compact/Bridge/C696PositiveWallOwnedWest.lean` now binds the completed
`PositiveWallOwnedWestCorner.impossible` argument to all four original
wall charts. The charts are identity, diagonal swap, half-turn, and
half-turn after swap. Their original role tables are:

    wall        = [8,9,10,11]
    paired      = [5,2,2,5]
    central     = [6,6,7,7]
    singleton   = [1,0,4,3].

The paired corners' empty exact auxiliary assignments exclude both
chart points (1.6,3) and (1,2.4). `CornerBudgetReach.upper_left` therefore
proves their genuine outward point (.8,3). With their original points
(1,3) and (1,3.086), these form the triangle used in the closure.

If the actual central square owns chart point (1,2), actual disjointness
and a positive canonical wall frame force

    2d-t <= W.loV,
    W.hiV <= 3d-.914t,
    0 < t < .172.

The wall's actual northeast closed vertex lies strictly inside the
paired corner's triangle, contradicting disjoint interiors. Thus
`frame_excludes` closes that entire original sector, independently of
both singleton signs and independently of any missing-center premise.
`canonical_sine_negative` records the resulting strict negative sine
for every signed canonical wall representative in this branch. The
axis-parallel boundary is included in the exclusion.

Ending independently hand-audited all four role tables, query points,
frame equivalences, containment and full disjointness transport. This is
source-level mathematical validation only: no Lean compilation was run.
The complementary central-point-missing sectors remain open.

## Negative left-singleton sign cannot be discarded locally

The suggestion that the negative-bottom / positive-central local branch
forces a positive left singleton fails by continuity. This is a hand
argument, not a newly exact-checked witness. Start from the previously
exact-checked five-square witness, whose left singleton is the axis
square `[0,a] x [.92,.92+a]`. Its OL support gap is
`499/50001250`, and its LA support gap is `1499957/2011250000`, both strict.

Rotate that left square clockwise about its lower-left vertex `(0,.92)`.
For a sufficiently small positive rational half-angle epsilon, set

    l=(1-epsilon^2)/(1+epsilon^2), r=2epsilon/(1+epsilon^2),
    L.c=l, L.s=-r, L.loU=-.92r, L.loV=.92l.

Its left containment remains exact. Its bottom remains positive, all
strict anchors and pair separators persist, and the original excluded
markers/auxiliaries have positive exclusion margins. In particular,
the corner's relative U coordinate becomes `l-.08r<a`, preserving
strict ownership of `(1,1)`. The two surviving relevant support modes
remain `upper_L(O.U)<O.loU` and `upper_L(A.U)<A.loU`. Thus actual L/A
and O/L coupling alone cannot exclude the negative-L sign. Both signs
must remain in the full packing analysis; no false sign theorem was
written.

## Omitted bottom wall inherits a genuine negative sign

`Compact/Geometry/NegativeBottomNextWall.lean` now proves a complete
two-square support implication: a negative canonical O with t<=.2,
actual bottom containment and missing corner cannot coexist with a
nonnegative canonical D owning `(2,.914)` and missing `(3,.914)`.
The missing next marker belongs to the real paired southeast corner.

All SAT alternatives are retained. The transverse possibilities vanish
by the signed tilt bounds. On D's U axis, the true O bottom wall and
corner lower face force `upper_O(D.U)>U_D(2,.914)`, contradicting the
strict D marker. On O's U axis, split the genuine next-marker exclusion
into the exhaustive upper-U and lower-V faces. Both yield nonnegative
continuous margins, with strictness supplied by a>1. The only quadratic
certificate is

    1-2.414d+1.5d^2
      =1.5(d-1207/1500)^2+43151/1500000.

The original adapter `Compact/Bridge/C696NextBottomWall.lean` supplies
the small-angle entrance internally from `PositiveWallPositiveLeft.cuts`
and supplies the bottom sign internally from the completed original
`C696PositiveBottomWest` theorem. Its public `canonical_sine_negative`
has only the original family plus actual missing corner, center and west
point as branch premises. Every canonical representative of actual
bottom wall9 then has strictly negative sine. No bottom-wall orientation
or numerical pose interval is assumed. This rules out its entire
nonnegative orientation sector; the actual negative wall and paired
corner/right-wall continuation remain. Source is uncompiled.

## Entire original missing-west branch closed in source

The preceding sign implication has now been strengthened to
`C696NextBottomWall.missing_west`: the original family, owner0 missing
`(1,1)`, owner6 missing `(2,2)`, and owner6 missing `(1,2)` imply False.
No frame, sign, support selector, or angle bound remains as an extra
premise of this public theorem. This closes one original branch; the
owned-west branch remains a separate obligation.

The new step keeps actual bottom wall9 and paired southeast owner2.
`C696PositiveWallOwnedWest.frame_point` is the contrapositive of the
paired-corner triangle argument: every actual positive canonical wall
in its wall chart owns `(1,2)` itself. It requires no adjacent-central
ownership. A negative physical frame for bottom wall9 becomes positive
under the diagonal chart, so actual wall9 owns physical `(2,1)`.

`NegativeBottomInnerWall.impossible` then closes all four O/D SAT
selectors. For any negative canonical normal `(d,-r)`, actual O bottom
containment, missing corner, marker and side greater than one imply

    upper_O(d,-r) > 2d-r.

The proof splits only at the relative angle order, with nonnegative
unit-circle defects and strictness supplied by the side. This conflicts
with a forward longitudinal separator because D strictly owns `(2,1)`.

For the transverse axes, O's true northeast closed vertex has `X>2`
and `Y>c_O>.914`. The last inequality follows from the already bound
`t_O<.2`. Hence for every x>=0,y>0,

    upper_O(x,y) > 2x+.914y.

This conflicts with each forward transverse separator because D owns
its original marker `(2,.914)`. Reverse directions are excluded by the
existing complete original-seed SAT selector. The result uses no
virtual coordinate wall and no unproved point such as `(1,2.88)`.

Files are source only. Root and ending independently hand-reviewed the
support identities, signs, actual vertices and original chart binding;
both passed. No Lean compilation or computational verification was run.

## Whole original C696 exclusion now sourced

`Compact/Geometry/OwnedWestBottomAngle.lean` completes the complementary
owned-west branch for both left-singleton signs simultaneously. The
original O marker exclusion has two exhaustive upper faces. Its upper-U
face and genuine corner lower-U face give `1<c+.086t`, hence `t<.172`.

For the upper-V face, the true bottom wall gives `B(c,t)<2t+.914c`.
An exact continuous cubic comparison forces `t>.47` and `c+t>1.35`.
The cubic endpoint margin is `14141/10000000`; it is not a sampled or
numerical bound. Both actual O/A transverse separators then fail:

* On O's axis the genuine central center-U cap and northwest-V cap give
  `lower_A(t,c) <= t+1.35c+19/280`. The strict original O face exceeds
  this bound because
  `c*(B-t-1.35c-19/280)=(c+t-1.35)+.35t^2-(19/280)c>0`.
* On A's axis, the full O bottom-wall defect and marker defect yield a
  sum of nonnegative terms plus `c*C*(c+t-1.35)>0`. The additional
  coefficient is `.65c-ct+.914t-t^2 >= .13c >=0`.

The central tilt restriction used in the uniform remainder follows from
actual ownership of `(1,2)` and the genuine northwest face cap. That cap
retains the original missing northwest marker and foreign singleton
point `(1,1.6)`. No left-sign assumption, absent top seed or surrogate
wall is introduced.

The original adapter `Compact/Bridge/C696OwnedWestClosure.lean` exports

    excludes : ExcludesCase 696.

It uses the completed center-first original-packing normal form, whose
actual bottom chain gives `-O.s>1/5`, while the new owned-west argument
gives `-O.s<1/5`. Every geometric premise is bound to the unchanged
original family and its actual owners. Root and ending independently
hand-audited the mathematical estimates; ending additionally audited
every original query coordinate, auxiliary exclusion, central crosspoint
projection, side equality, containment and disjointness binding. All
passed. The Mathlib multiplication-direction issue caught in review was
repaired. This is a whole-case source result, still **uncompiled**; no
Lean replay or end-to-end validation is claimed.
