# Actual C981 common-point sector

Current status: the later ordinary-wall and double-wall endings reduce
C981 to 49 pending representative obligations in the assembled source.
The last section records the still-open full-wall row 4. New symbolic
source remains uncompiled. Earlier sections below are retained research
snapshots; their individual sector results are not whole-vector claims.

`Compact/Geometry/C981CoupledSector.lean` proves that the actual two squares
share H=(2,1293/500)=(2,2.586) in the stated orientation sector.

A owns (2,2.26), (2.26,2), (2.35,2.35), misses (2.35,1.65), the foreign
B marker (1.65,2.35), and (3,2.4). In a positive shallow frame
0<=sA<=cA, the two possible lower faces at (2.35,1.65) both force H.
The crucial strict short-vector margin is
0.35²+0.936²=0.998596<1. The other face alternative uses the missing
right point and sA+0.186cA<=1. Axis-aligned A is included.

B owns (1.65,2.35), (1,2.4), and (1.74,3), and misses (1,3).
Its own left point makes the corner's lower U band strict, so that missing
corner can only use upper V. For 2cB/3<=sB<=cB, this upper V cap and
side>1 force H's lower V band. The exact remaining projection satisfies
sB+0.414cB<=1 because

    1-(sB+0.414cB)²
      = 0.828cB(cB-sB)+0.000604cB² >= 0.

All other H bands follow directly from B's strict anchors. Both square
sides are only assumed greater than one; there is no side upper bound,
congruence condition, enclosure, container bound, or assumed SAT separator.

`Compact/Bridge/C981CoupledSector.lean` uses the actual transformation
(x,y)->(y,4-x), with A=owner5, B=owner6, and corner=owner3.
The corner point (1,3) is the transformed original point (3,3), obtained
from owner3's real merged-corner seed and original packing disjointness.
The bridge's original query soundness uses the existing normalized-packing
contract; no new seed or foreign-point assumption is introduced.

The literal sector catalogue is [8,50,51,53]. The adapter exports
`frames_exist`, `excludes_sector`, and `remaining`. For every actual
packing with one of those ownership vectors, every chosen pair of positive
face frames satisfies at least one explicit remaining alternative:

- A.c < A.s;
- B.c < B.s;
- B.s < (2/3) B.c.

These are remaining orientations, not admissions or a completed vector proof.

## Why the two central placements do not yet close V53

V53's B owns both diagonal endpoints (2.26,3) and (3,2.26).
In a positive frame their strict transverse span gives
0.74(cB+sB)<side<=1.001. Thus B already avoids the near-diagonal
orientation range covered by this common-point sector. Reflecting the sector
and using the other central neighbor alone does not remove the real shallow
orientation alternatives. A complete V53 ending must also control the
longitudinal separation between its actual central squares and the walls.

The useful full-square support observation retained for that next step is:
in the steep B sector, the actual band corner formed from U(1.74,3) and
V(1.65,2.35) has coordinates

    X=1.74c²+4.65cs-2.35s²,
    Y=2.35c²+3s²+0.09cs.

When s>=0.6 and 0<=c-s<=0.2, X>=2.02 and Y>=2.35, using
X-2.02=(c-s)(4.09s-0.28(c-s)) and c²+s²=1. This controls a
longitudinal support that cannot be inferred from the single owned marker.
It is mathematical working evidence, not a further connected exclusion.

## Exact local witness against the pair-only route

The shallow complementary branch admits two full, disjoint squares with
the currently used A/B point premises. In the standard transformed
coordinates, let both sides be 1001/1000. Take A axis-aligned with

    1.99 < x < 2.991,    1.74 < y < 2.741.

Take B with c=99/101, s=20/101 and bands

    1299/1000 < U < 23/10,
    17/10 < V < 2701/1000.

Here 99²+20²=101², so B is an exact square. Its strict owned points
include the central marker (1.65,2.35), both left points (1,2.26),(1,2.4),
and both top points (1.6,3),(1.74,3). Its closest upper-U check is the
last point, where

    U(1.74,3)=11613/5050 < 23/10.

It misses the corner (1,3) through upper V:

    V(1,3)=277/101 > 2701/1000.

A owns the three original elbow points and misses its lower marker, B's
marker, and the right point. The original extra auxiliary (2,1.74) is on
A's boundary, hence outside. Both squares lie inside the container. They
are strictly separated in x, since B's largest x-coordinate is

    (99*(23/10)-20*(17/10))/101 = 1937/1010 < 199/100.

This is an exact hand-algebra witness for the two-square premises, not
a twelve-square packing and not a compiler-checked witness. It demonstrates
why V53 needs its other central square and actual upper-wall geometry.

## Full-orientation outer reach of the other central square

`Compact/Geometry/CentralOuterReach.lean` now proves the following complete
local implication, with the full square and all orientations retained. A
side-greater-than-one square owning (2,2.26), (2.26,2), and (2.35,2.35),
and missing (2.35,1.65), (1.65,2.35), (3,2.4), and (2.4,3), contains
both (2.35,2.65) and (2.65,2.35). There is no side upper bound or container
premise. Unit-length target differences are allowed because the square's
side is strictly greater than one.

The additional upper-point exclusion matters. In a shallow positive frame,
if the lower marker misses lower V, the other central marker misses lower U.
Then (2.4,3) cannot miss upper U: that strip would have width at most
sqrt(0.75²+0.65²)=sqrt(0.985)<1. It therefore misses upper V, which supplies
the target's previously unresolved lower V band. In the other branch the
right outer point supplies lower V. Swapping coordinates handles the entire
remaining orientation sector.

`Compact/Bridge/C981CentralOuter.lean` derives, for the original V53 owner 7,
the strict points (1.65,2.65) and (1.35,2.35). All four missing points come
from the original exact ownership query. In particular (1.6,3) belongs to
the upper wall, and (1,2.4) belongs to the left wall. The adapter exports
`C981CentralOuter.v53_points`; it does not assert `ExcludesVector` and does
not alter the pending representative count. This source has not been compiled.

The outstanding coupled step is now concrete: upper wall 11 must avoid the
actual owner-7 point (1.65,2.65), while containing (1.6,3), (1.74,3), and
(2,3.086), remaining below y=4, and being disjoint from the full northeast
square. No contradiction from those weaker fixed-point premises alone has
yet been established; the central square's complete support remains available.

## Remaining continuous cycle, and a hand-derived face reduction

The actual mutual disjointness of the two opposite central owners 5 and 7
must also be retained. Their compulsory triangles alone allow positions
which overlap near (2,2); considering either square separately loses this
interaction. A potential shared ending is to show that each central owner
must contain (2,2) when its two adjacent wall squares are present.

There is a short exact reduction for an elbow owner that misses (2,2).
In its positive shallow frame c>0 and 0<=s<=c, the owned points
(2,2.26), (2.26,2) put the center's V value strictly inside the V strip,
so the center can only miss lower U:

    2(c+s) <= loU.

With the actual missing points G=(2.35,1.65), R=(3,2.4), and T=(2.4,3),
the two outer upper faces are then forced:

    loU+side <= 3c+2.4s,
    loV+side <= -2.4s+3c.

For the second inequality, T's U upper band follows from the center bound
because 0.4c+s <= 0.7*sqrt(2)<1 on this shallow sector. T's remaining
non-upper-V bands follow from the anchors. R cannot miss lower V, since
together with the T upper-V cap this would give side<=0.6(c+s)<1.
If R missed upper V, the owned (2,2.26) would force s<0.14c; then G's
U bands are strict, so G must miss lower V, giving side<=0.75c-0.65s<1.
R's remaining escape is therefore upper U. Swapping coordinates covers
the other positive sector.

This last reduction is recorded as hand algebra, not as an additional Lean
theorem. It reduces the unresolved central/wall support cycle to a concrete
continuous face configuration, but it does not establish that cycle's
contradiction. No whole-vector exclusion or pending-count change follows.

## Actual wall segments remove the middle-angle center escape

`Compact/Geometry/CentralEscapeSegment.lean` adds a continuous reduction.
For an NE-standard elbow A in a positive shallow frame, suppose the actual
right neighbor R contains (3.086,2) and (3,2.4), A and R are disjoint, and
A misses (2.4,3). If A misses (2,2), its anchors force

    2(c+s) <= loU,    hiV <= V(2.4,3).

The first bound follows because the center is already strictly inside the
V strip. The second uses .4c+s <= .7(c+s) < 1 for 0<=s<=c.
The real segment in R contains

    P=(60731/20000,223/100)=(3.03655,2.23),

using interpolation weight 23/40. Its squared distance from (2.4,3) is
.9980959025<1. When (16/25)c<=s<=c, its U displacement from (2,2)
satisfies 1.03655c+.23s<=1. An exact polynomial proof uses

    (s-.64c)(s+.13c) >= 0,    c^2+s^2=1.

These two estimates and the elbow anchors place P strictly inside A,
contradicting the actual neighbor's strict ownership. Swapping coordinates
uses the actual top-wall segment for the other half of the positive frame.
Thus a center-escaping elbow has

    s < (16/25)c  or  c < (16/25)s.

`Compact/Bridge/C981V53EscapeAngles.lean` supplies both wall segments from
the original V53 query. The SE roles are [5,10,9], transformed by reflection
in y; the NW roles are [7,8,11], transformed by reflection in x. The actual
SE/NW disjointness makes at least one elbow miss (2,2).
`v53_narrow_one` therefore restricts at least one of their guaranteed
positive frames to the stated remaining sectors. This applies without a
neighbor side bound, container bound, singleton seed, or assumed SAT face.

The scalar calculation received an independent mathematical source review;
neither new module has been compiled. No whole vector is removed. The
remaining near-axis escape needs both adjacent walls' complete supports:
a sufficiently small positive elbow angle can avoid a single axis-aligned
right wall by approaching equality at the top exclusion, so a single-wall
center-forcing assertion would be too strong.

## Whole V53 source ending from the two adjacent physical walls

The preceding one-wall obstruction used only the weaker missing top point
(2.4,3). It does not satisfy the stronger original consequences now used.
The top wall's actual marker, high point, lower auxiliary exclusion, and
container force its strict point (2.56,3), by `WallLowerReach.point` after
the exact symmetry. Its original strict segment therefore contains (2.5,3).
The right wall similarly contains (3,2.5). These are consequences of the
actual neighbors, not added geometric hypotheses.

`CentralWallCenter.point` now assembles a whole all-angle geometric ending.
For a positive shallow central frame, the real right-wall segment first
removes s/c >= 16/25. If the center still escapes, the stronger top missing
point forces the strict central point

    H=(3,2+z),  z=s/(1+c).

Every positive reindexing (r,t) of the actual right wall places H strictly
inside its transverse strip. Disjointness selects its lower longitudinal
face. The actual marker and container then give

    tz < .086r,    rtz < 1-r-.086t^2.

These imply z<1/5 and therefore 12s<5c. The same bounds force the wall's
positive angle strictly above the central angle. Original G exclusion now
selects the central lower transverse face. Full-square SAT has exactly two
remaining forward longitudinal separators: the central axis or wall axis.

`CentralWallParallelMargin.parallel_margin` excludes the first using the
parent's continuous endpoint/quartic identity. `CentralWallLongitudinal`
excludes the second using two supporting lines of the unit circle and a
concave quadratic whose endpoints have margins at least 1/50 and 9/1000.
`CentralWallPairSupport` retains the full square supports and the physical
container inequality in both branches. Swapping coordinates covers the
other half of every positive central frame. No side upper bound is needed.

The new original adapter `Compact/Bridge/C981WallElbows.lean` uses both
actual V53 elbows, with roles [5,10,9] reflected in y and [7,8,11] reflected
in x. Its `Check` includes all original owned points and all actual missing
points used by the theorem. Both owners 5 and 7 contain (2,2), contradicting
their original disjointness. The parent's exact literal premise scan,
recorded in `evidence/c981-wall-elbows-premise-scan.json`, gives sixteen
matching representatives:

    0,7,8,19,22,44,50,52,53,66,110,111,113,114,115,116.

`C981WallElbows.covered_excluded` now contains this entire checked list.
Inspection of the earlier literal endpoint/diagonal lists and the separate
V116 ending gives overlap exactly 7,110,116. The thirteen new entries are
0,8,19,22,44,50,52,53,66,111,113,114,115. `C981Compact` consumes all sixteen
whole-vector endings and records this exact difference by an ordinary
kernel finite check in source. Its pending contract is now 55 full vectors,
down from 68; `SourceAssembly.Pending.case981` consumes that updated contract.

This is a complete original-vector source proof, independently reviewed
mathematically at the parent. None of the new modules has been compiled.
The wall-axis scalar proof also received an independent hand audit from
the kernel worker: its displayed endpoint estimates strengthen to
.02031538... > 1/50 and .009255 > 9/1000, and its small-sector factor and
both unit-circle supporting-line identities agree exactly.
No compiler, solver, generator, or computational worker was run by this
worker. The finite catalogue scan was run by the parent; the pending source
partition was updated only after that exact scan. Kernel replay remains
the acceptance boundary.

## Double-auxiliary walls: complete continuous source ending

A second whole center theorem is now written in
`Compact/Geometry/DoubleAuxWallCenter.lean`. In the canonical NE chart,
the right wall may own both `(3,1.74)` and `(3,2.4)`, provided its actual
outer point `(3,1.6)` is excluded. The top wall keeps the ordinary lower
auxiliary exclusion. All three real squares, their common side, wall
containment and actual interior disjointness remain in the theorem.

The extra excluded point must not be dropped. An earlier near-axis
three-square counterexample owned that point and therefore refuted only
a weaker point/segment relaxation, not the original vector. Conversely,
the double-auxiliary wall alone need not own `(3,2.5)`: after moving it to
the left wall, the exact choice

    c=20/29, s=21/29, a=1001/1000,
    loV=11/29, loU=(21/20)*(11/29+a)

owns `(.914,2),(1,1.74),(1,2.4)`, misses `(1,1.6),(1.74,2)`, and misses
`(1,2.5)` above its U band. This local obstruction is addressed by keeping
the wall's full support rather than asserting a false stronger point.

The new proof swaps the difficult central-angle branch, so A is shallow
and its top wall T owns both horizontal auxiliary points. If `s/c>=1/4`,
the original weaker top exclusion `(2.4,3)` already gives the strict
half-angle crossing `(3,2+s/(1+c))`: the needed inequality is simply
`.4c+s>=.6`. The existing whole right-wall SAT endgame then applies. Its
proof has been extracted as `CentralWallCenter.center_of_crossing`, with
no change to the existing all-angle theorem's assumptions.

For `0<=s/c<=1/4`, suppose A contains `(2.5,3)`. Genuine A/T disjointness
and the exact missing `(1.6,3)` select T's two lower faces:

    loU_T >= 1.6 C + 3 S,
    loV_T >= -2.5 S + 3 C.

The alternative face at `(1.6,3)` would put the same point strictly inside
T, using the actual inward exclusion `(2,2.26)` and short projection
bounds. The top container wall now forces the strict defect

    delta = 1 + .9 C S - C - S > 0.

This excludes axis frames and forces `C+S>11/9` and `S>21C/80`. Full-square
SAT leaves only the two forward transverse axes. The parent's continuous
scalar module `DoubleAuxWallMargins` proves

    cS-sC > 0,
    (C+S-1)(cC+sS)-.9sC >= 0,
    C(cS-sC)(.5c+.74s)-delta >= 0.

These rule out the two remaining axes using exact support formulas and
the actual wall inequality. Thus A cannot contain `(2.5,3)`, restoring the
original right-wall ending without falsely asserting T contains it.
`DoubleAuxWallCoupling` gives the geometric derivation; no orientation
sampling or additional packing assumption is present.

The finite adapter `Compact/Bridge/C981DoubleWallElbows.lean` has four
placements: ordinary/double SE and ordinary/swapped-double NW. Its three
pairs derive the center of both distinct actual owners. The hand-inspected
candidate literal rows are `1,20,21,23,51`; each is guarded by an ordinary
finite original-query check in the source. Row4 is deliberately excluded:
its wall owns both outer auxiliary points and does not meet the required
missing-point premise. Full finite scanning and Lean replay remain the
parent's validation steps. No catalogue or pending registry is altered by
this worker's source assembly.

The parent's exact all-117 original-query scan completed and found one
additional genuine match, row112. The final six are
`[1,20,21,23,51,112]`; the receipt is
`evidence/c981-double-wall-elbows-premise-scan.json`. All six are disjoint
from the earlier whole-vector source endings. `C981Compact` now consumes
all six and records the remaining49 whole representatives by an ordinary
kernel finite theorem in source. `SourceAssembly.Pending.case981` uses
this exact smaller contract. This changes no original theorem assumption
and does not count C981 as a completed original case. All new source still
awaits Lean replay; the parent independently reviewed the continuous
argument and the actual ownership adapter.
## Row 4: full wall segment, remaining coupled obligation

Row 4 is not among the six new double-wall exclusions. Its right owner has
all four auxiliary indices `{8,9,18,19}`, so the missing point used in
`DoubleAuxWallCenter.point` is genuinely owned instead. No missing point is
silently transferred into this case.

Use coordinates `(x,y)=(4-oldY,oldX)`. Owner 5 becomes the NE inward elbow A,
owner 9 becomes its ordinary right wall W, and owner 10 becomes the top wall
T. Their original strict points are:

| Square | Original points in this chart |
| --- | --- |
| A | `(2,2.26)`, `(2.26,2)`, `(2.35,2.35)` |
| W | `(3.086,2)`, `(3,2.26)`, `(3,2.4)` |
| T | `(2,3.086)` and `(x,3)` for `x=1.6,1.74,2.26,2.4` |

The actual outer central square, owner 6, becomes B with strict points
`(1.65,2.35)`, `(1,2.26)`, and `(1,2.4)`. Owner 7 is the opposite SW
elbow; the ordinary-wall center theorem already puts the center strictly
inside that square. All square shapes, side equality, container premises,
and physical pairwise disjointness must remain available in the coupled
ending.

`Compact/Geometry/FullAuxWallEscape.lean` now proves an exact residual
sector reduction for the actual A/W/T squares. In a positive shallow frame
`(c,s)`, if A misses the center then

```
0 < s,  4s < c,
2(c+s) ≤ loU < 2c + 2.26s,
3c - 2.5s < loV + a ≤ 3c - 2.4s,
A.Inside(2.5,3).
```

Every larger angle closes by the previously proved moderate crossing and
the actual right-wall separating-axis argument. The opposite orientation
uses the ordinary wall's stronger point and its corresponding crossing.
The displayed reduction is source only; it does not prove row 4, alter its
pending status, or assume any of the absent wall exclusions.

The remaining gap is a coupled support contradiction involving the actual
outer central B and/or the opposite elbow and its wall neighbors. A
point-only completion is insufficient. In the reflected original chart,
the old four-square template has all its usual anchors except the left
wall exclusion at `(0.76,1.87)`; that wall instead owns the strict segment
`{1}×[1.6,2.4]`. Its old terminal left-wall lemma therefore cannot be reused.

The current coupled route retains B, C, A and T as complete squares. In
addition to its strict center point, C has the genuine foreign bottom-wall
point `(1.74,1)` excluded; replacing C by its center alone loses the relevant
support restriction. The proposed support cycle is A/T, T/B, B/C, C/A.
The narrow A face strip also implies `A.Inside 2 (12/5)` directly. Neither
this extra point nor the cycle description is a whole-vector proof.

One exact reduction within the A/T edge illustrates the remaining work.
Write the positive normals as A=(c,s), T=(C,S), and put
`beta=c*S-s*C`, `alpha=c*C+s*S`. In T's lower-V escape at the genuinely
foreign A point `(2.5,3)`, measure its lower-face deficiencies from its
owned point P=(2.4,3):

```
x = 2.4*C+3*S - T.loU,
y = -2.4*S+3*C - T.loV.
```

The actual owned `(1.6,3)` gives `x>0.8*C`; the lower-V escape gives
`0<y<=0.1*S`. If the full-square separator is A's V axis and `beta>=0`,
then A's strict `(2.5,3)` gives `beta*x+alpha*y<0.1*s`, hence
`0.8*C*(c*S-s*C)<0.1*s`. Thus this mode constrains the relative angle
continuously, instead of furnishing the false missing outer endpoint.
This calculation has been checked symbolically by hand only. The other
A/T separator, T's upper-U mode, and the coupled B/C transitions remain
open. No additional row is removed from the pending catalogue.

### Signed support-cycle checkpoint (11 October, source reasoning only)

The complete top-wall square can be restricted continuously, without
pretending it is axis aligned. Put `r=s/c<1/4` for A and normalize T's
frame to `(C,±S)` with `0<=S<=C`. Both longitudinal A/T axes overlap by
the actual inward A point, A's strict `(2.5,3)`, and T's two outer row
endpoints. Only the two forward transverse axes remain.

For positive T with angle at least A's, let `k=cS-sC`,
`alpha=cC+sS`. The A-axis separator and the owned row endpoints imply

    8 C k < s.

Writing `q=S/C`, this is `8c q<s(9+q^2)`, so `q<(5/4)r`.
The T-axis separator instead implies

    k(.5c+.74s)<.1S,

which gives `q<(4/3)r`; here `c(.5c+.74s)>.4` follows from the
actual narrow A angle. If T's positive angle is below A's, the same
final upper bound is immediate. Thus positive T has `S/C<(4/3)r`.

For negative T, the T-axis separator is impossible: the full A support
strictly exceeds its projection at `(2.5,3)`, while T's owned `(2.4,3)`
bounds its lower face below that projection. The other separator gives

    8c q<s(1+9q^2),

and hence `q<r/(8-9r)<=(4/23)r`. Both signed conclusions use the full
square support and retain all original owned points; neither is a
whole-row exclusion. These calculations are hand-audited, not Lean
accepted.

The opposite elbow C also requires signed axes. In particular, for a
negative canonical C frame `(C,-S)`, its V normal `(S,C)` is a genuine
forward longitudinal direction; it must not be discarded as a transverse
axis merely because the coordinate is named V. If

    epsilon=A.loU-2(c+s),  v=A.loV-2(c-s),
    k=cS+sC,  alpha=cC-sS,

that selector requires

    k*epsilon+alpha*v >= C.hiV-2(C+S)>0.

The weaker estimate `v<-.4s` initially left a near-diagonal case. Retaining
the full existing face bound `v<c-1-.4s` removes that apparent gap. Put
`dx=c*epsilon-s*v`, `dy=s*epsilon+c*v`. The original narrow angle gives
`c>=24/25` and `1-c<=(2/3)s^2`. Consequently

    dy < 0,
    dx+dy < 1-c+s-(57/50)cs-(17/50)s^2
           <= s*(1-(127/120)c) <= -(2/125)s < 0.

The exact residual is `S*(dx+dy)+(C-S)*dy`, hence strictly negative for
every canonical opposite angle. `FullAuxWallLowerCorner.lean` now proves
the scalar estimates and their original-square support consequence,
`opposite_v_impossible`. The parent independently checked the polynomial
expansion and estimates; the Lean source is not yet compiled. An earlier
informal argument omitted this selector, but the subsequent signed-axis
audit retained it and this stronger actual face strip now eliminates it.

In the other negative-C selector, separation on A's U axis, C's genuine
missing `(1,1.74)` has exactly two lower-face escapes. Its lower-V escape
contradicts the support bound; its lower-U escape yields `S<C/2` and
`C.hiU-2(C-S)<1/10`. Together with C's existing strict center and lower
crosspoint this forces `C.Inside(1.2,2)`. Such a left reach makes the
subsequent B/C support cycle force the V-strip at `(1.6,3)`. For negative
B, and for positive B with `13*B.s<=B.c`, the U-strip follows from B's
original points and contradicts T's actual endpoint. Positive B with
`13*B.s>B.c` has a genuine remaining upper-U escape
`B.hiU<=1.6*B.c+3*B.s`; it must be retained in the full B/T/left-wall
cycle. This last face was found by the point-band audit before any Lean
theorem was written. The whole row remains open. This was the intermediate
checkpoint; the negative-C continuation is superseded by the complete
signed-sector source described below.

The actual lower-left and bottom walls must remain available for the
remaining selectors. Even a same-angle/axis-wall diagnostic illustrates
why C's missing bottom point alone is too weak: a lateral support chain
gives a necessary inequality

    c+s-c*s+.33*s^2 <= 1,

which is compatible at small positive s. No proof may replace the bottom
wall's full square by only that single exclusion and then assert the
opposite inequality.

### Negative-C sector completed in source; positive C still open

`FullAuxWallNegativeCycle.negative_opposite_impossible` now closes the
entire negative canonical C sector, including every canonical B angle.
The original ownership adapter is now written in
`Compact/Bridge/C981FullAuxNegative.lean`. Its `negative_frame_impossible`
derives every geometric entrance from representative 4, normalizes A and
B internally, eliminates A's steep positive frame using the genuine
ordinary right-wall reach, and derives C's lower crosspoint from the
actual left wall. Its `positive_residual` states that every canonical
frame of original owner 7 has strictly positive sine. No whole row or
original case is removed from the pending registry at this checkpoint.

The argument is continuous. Exhaustive A/C separation leaves one actual
support cut. C's genuine missing left point strengthens the earlier
angle bound to `4*S<C`, and forces the strict point `(1.1,2)`. Exhaustive
C/B separation then proves B's V strip at the genuine top-wall endpoint
`(1.6,3)`. Every negative B frame contains that endpoint outright.

A positive B frame must instead satisfy the upper-U cap
`B.hiU<=1.6*b+3*t`. Its genuinely foreign paired corner `(1,3)` supplies
`B.hiV<=3*b-t`. One separator is now impossible directly. The other gives

    a*(1+k) + alpha*v <= b+t+k*u,
    k=t*C+b*S, alpha=b*C-t*S, u>0, v>0.

The earlier A/C cut gives `u<.08`. Since `alpha>=0`, `k>=t`,
`k<=t+.25`, and `a>1`, the displayed inequality implies

    t^2/2 <= 1-b < .08*(t+.25),

so `t<.3`. Both upper caps now place the original left-wall marker
`(.914,2)` strictly inside B, contradicting packing disjointness. This
ending removes the longer left-wall angle-order argument entirely.
`FullAuxWallLeftMargins` and `FullAuxWallLeftOrder` are independent research
source; the completed signed-sector theorem does not import them.

The complementary positive-C sector has an exact reduction in
`FullAuxWallPositiveOpposite`: both surviving longitudinal selectors imply
that C's upper-U excess above its owned center lies in `(0,.1)`. Its
genuine missing bottom point then forces the lower-V face. These reductions
do not exclude the A/C pair by itself. The next signed sector is now also
complete in source, as described below.

The parent independently reviewed the support identities, sign coverage,
small-angle inequality, and final marker strips. All of this is source
and mathematical review, not compiler acceptance. Compilation remains
deferred until the full proof source is assembled.

### Positive C with nonpositive B completed in source

`FullAuxWallPositiveCNegativeB.impossible` excludes this entire signed
sector. It derives C's genuine bottom-face bound
`C.loV >= C.c - 1.6*C.s` and the shifted strict reach `(1.2,1.9)` from the
actual A/C separation, C's crosspoint, and the original bottom-wall point
`(1.6,1)`. It does not assume the stronger `(1.1,2)` reach from the other
signed sector. Exhaustive C/B separation then leaves two transverse axes.

Write B's frame as `(b,-t)`, with `0<=t<=b`. Missing the actual top-wall
point `(1.6,3)` gives `B.hiV<=3*b+1.6*t`. The genuine paired-corner seed
`(1,3)` has only two possible escape faces:

    B.loU >= b-3*t,  or  B.hiV <= 3*b+t.

The B-axis separator contradicts the owned C center immediately. The
C-axis separator, with the two genuine corner escapes, would require
one of the following quantities to be strictly greater than one:

    C*(2-b-t+.6*b*t) + S*(.6-b+t-.6*t^2),
    C*(2-b-.65*t^2-.65*b*t) + S*(-.05+.65*t^2-.65*b*t+t).

`FullAuxWallPositiveCNegativeBMargins` proves both are at most one on
the full canonical arcs using rational unit-disk bounds, without angle
sampling. The scalar identities and estimates were independently reviewed.

The original adapter now exposes `EscapingFrame` and `escaping_exists`,
reusing the same previously reviewed A normalization in both signed
sectors. `negative_upper_frame_impossible` binds the new theorem to row4;
the added bottom point is authenticated by original owner8's G11 under
the chart. `upper_positive_residual` proves every canonical frame of
original owner6 has strictly positive sine. Thus the exact original row4
residual has **both C and B strictly positive**. It remains open; no whole
row was registered, and none of this new source has been compiled.

