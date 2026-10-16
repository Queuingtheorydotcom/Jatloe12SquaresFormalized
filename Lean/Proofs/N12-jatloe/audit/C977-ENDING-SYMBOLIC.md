# C977: all four wall directions follow symbolically

Source-only derivation, 11 October 2026. This worker did not run Lean, Lake,
numeric producers, heavy searches, downloads, or background jobs. The new source
files are frozen for the parent's bounded replay:

- `Compact/Geometry/WallLowerCenterBarrier.lean`
- `Compact/Bridge/C977OppositeWallCenters.lean`
- `Compact/Geometry/WallCornerReach.lean`
- `Compact/Geometry/WallUpperMissingReach.lean`
- `Compact/Geometry/WallInwardCenter.lean`
- `Compact/Bridge/C977OppositeWallExtras.lean`
- `Compact/Geometry/CentralWingReach.lean`
- `Compact/Bridge/C977CentralWingReach.lean`

## Original-premise result and exact scope

Every normalized packing with the original C977 marker family satisfies

    centerY(owner10) > 21/10,
    centerX(owner11) > 21/10.

Together with the existing `centerY(owner8)>2` and `centerX(owner9)>2`,
this leaves only the wall branch `[false,false,false,false]`. These are
strict bounds on actual original centers, valid before choosing a complete
auxiliary vector. No angle bins, saved center polygons, search outputs,
SAT assumptions, or side upper bound occur in the geometric deduction.

The wall cuts leave **57 complete ownership vectors in one wall branch**,
down from 57 vectors in four branches. This excludes 171 of the previous
228 contexts uniformly. The further coupled argument below excludes one
whole vector, leaving **56 complete vectors in the all-upper wall branch**.
The shared central wing implications below remove six further vectors,
leaving **50 complete vectors in that single wall branch**. None of these
results establishes `ExcludesCase 977`.

The canonical packing is still exactly the previously proved original-or-
transpose alternative. No further symmetry normalization is assumed. The
strengthened missing corner, canonical corner bounds, full exact ownership
vector, and actual disjoint original squares are preserved.

## Generic four-point wall lemma

Let a square of side `a>1` be contained in `[0,4]^2`. Assume

    P=(457/500,2), Q=(1,12/5) are strictly inside,
    W=(1,87/50), T=(33/20,47/20) are not strictly inside.

Then its actual center has `Y>21/10`.

Reindex the four faces, preserving the physical square and center, so that
the first unit face normal is `(c,s)` with `c,s>=0`, `c^2+s^2=1`. Write
`U,V` for the two lower face offsets. Left containment gives

    c U - s(V+a) >= 0.                              (wall)

The point W is below Q on the same vertical line, so Q rules out W's
upper-U escape. Relative to P its V coordinate decreases by
`(43/500)s+(13/50)c`, so P rules out its upper-V escape. Hence exactly the
following two closed alternatives suffice:

    c+(87/50)s <= U,                                (WU)
    -s+(87/50)c <= V.                               (WV)

Zero components are retained throughout. The inequalities are closed for
outside faces, so tangencies are included.

### Lower-U branch

P rules out T's lower-U face, and Q rules out T's upper-V face. If T escaped
through upper U, combining that escape with (WU) would give

    a <= (13/20)c+(61/100)s <= 1.

The final inequality follows from the unit normal and

    (13/20)^2+(61/100)^2 = 3973/5000 < 1.

This contradicts `a>1`. Therefore T must take its closed lower-V escape:

    -(33/20)s+(47/20)c <= V.

Multiplying (WU) by s and this inequality by c gives

    Y > 47/20 -(61/100)s^2 -(13/20)cs +(c+s)/2.

The strict sign comes solely from `a>1` and `c+s>=1`. The elementary unit-
normal estimates

    c+s >= 1+(4/5)cs,  s^2<=1,  cs<=1/2

then give

    Y > 57/20 -(61/100)s^2 -(1/4)cs
      >= 57/20 -61/100 -1/8
       = 423/200 > 21/10.

To justify the first normal estimate without square roots, use
`1<=c+s<=3/2` and `(c+s)^2=1+2cs`. Their product inequality
`(3/2-c-s)(c+s-1)>=0` gives the claimed bound.

### Lower-V branch

There is an exact identity

    cY = s[cU-s(V+a)] + V + (a/2)(1+s^2+cs).

Use (wall), (WV), and `a>1` to obtain

    c(Y-21/10) > (1+s^2+cs)/2-s-(9/25)c.             (F)

The right side is nonnegative for every `0<=c<=1`, `s>=0`:

- If `s<=18/25`, replacing c by 1 in the nonpositive coefficient
  `c(s/2-9/25)` bounds it below by
  `s^2/2-s/2+7/50 = (s-1/2)^2/2+3/200 > 0`.
- If `s>=18/25`, write it as
  `(s-1)^2/2+c(s/2-9/25) >= 0`.

Thus `c(Y-21/10)>0`, and `c>=0` implies `Y>21/10` without division by c.
If c=0, the same displayed strict inequality is a contradiction, so no axis
endpoint is silently dropped.

## Actual C977 entrances

The established ordered-owner codes and the complete original auxiliary
domains supply the following data, uniformly over all 57 vectors:

| Application | Owned marker P | Owned auxiliary Q | Foreign point W | Missing marker T |
|---|---|---|---|---|
| Right owner10/code16384 | `(1543/500,2)`, marker14 | `(3,12/5)`, auxiliary19 | `(3,87/50)`, auxiliary8 of owner6/code512 | `(47/20,47/20)`, marker10 |
| Top owner11/code32768 | `(2,1543/500)`, marker15 | `(12/5,3)`, auxiliary7 | `(87/50,3)`, auxiliary14 of owner7/code2048 | `(47/20,47/20)`, marker10 |

The right application reflects x to `4-x`. The top application pulls back
by `(x,y) -> (y,4-x)`, implemented as `pullX (pullSwap q)`. These are local
transports of the lemma only: the actual packing and its canonical frame
are unchanged. In both applications T becomes `(33/20,47/20)`.

Foreign strict ownership and original packing disjointness supply W's
missing-point premise. The existing `unused_marker_ten` theorem supplies T's
missing-point premise for every original square. All new finite membership
checks use ordinary kernel `decide`, with no new native checks or axioms.
The imported historical coverage still has its previously documented trust.

## Stronger strict wall points

The original corner-anchor wall lemma reaches `(1,133/50)=(1,2.66)`.
In its two-lower-face branch, the necessary projection vectors are
`(6/25,79/100)` and `(-37/50,33/50)`, whose squared norms are respectively
`6817/10000` and `1229/1250`, both below one. In its wall-controlled branch,
the old bound `c+s>=1+(4/5)cs` suffices because `2.66-1.87=.79<.8`.
This is `WallCornerReach.point`.

The new lower-W/upper-T hypotheses force `(1,64/25)=(1,2.56)`.
The lower-U mode uses the already proved T lower-V escape and vectors
`(0,41/50)` and `(-13/20,21/100)`. The wall-controlled mode uses
`c+s>=1+(41/50)cs`, which follows from `c+s<=10/7` and the unit normal.
This is `WallUpperMissingReach.point`.

The established original-owner entrances therefore imply the strict points
`(1,2.66)` in owner8, `(2.66,1)` in owner9, `(3,2.56)` in owner10, and
`(2.56,3)` in owner11. These geometric lemmas are separate reusable source
theorems; no additional whole-vector exclusion is counted merely from the
availability of those stronger points.

## A complete coupled exclusion of one vector

Suppose additionally that owner10 owns auxiliary16 `(113/50,2)` and owner11
owns auxiliary5 `(2,113/50)`. The same local transforms put each wall square
in the generic reflected-left frame, now with an **owned** point
`D=(87/50,2)`, in addition to strict P,Q and missing W,T above.

There is a small exact sector argument, independent of containment:

1. P rules out T's lower U; D rules out T's lower V; Q rules out T's upper V.
   Thus `U+a <= (33/20)c+(47/20)s`.
2. W cannot be upper U or upper V, using Q and P respectively. Its lower-U
   alternative is incompatible with T's upper U since the intervening
   projection has length at most `sqrt(3973/5000)<1<a`. Thus
   `V >= -s+(87/50)c`.
3. Comparing strict D with these two faces yields
   `9c<35s` and `37s<13c`.

The unit normal and this sector give the coarse exact bounds

    c>=15/16,  s>=6/25,  c+s<=13/10.

For the sum bound, the product
`(13c-37s)(37c-13s)>=0` gives `1538cs<=481`; combine it with
`(c+s)^2=1+2cs`. These are full continuous normal bounds, not samples.

The strict upper-U inequality for owned D and lower-V inequality for W give

    Y > 87/50+(13/50)s^2+(37/50)cs+(c-s)/2
      >= 87/50+15/32+(31/160)(6/25)
       = 9021/4000 > 9/4.

Here strictness uses `a>1` and `c-s>0`; the nonnegative squared term is
discarded. The side cap and normal-sum bound give an axis support half-width
at most `69/100`. D, Q, and P then supply the remaining center bounds:

    21/20 <= X <= 7/4,       9/4 <= Y <= 59/20.

This is `WallInwardCenter.center_box`. It requires no container, angle-bin,
or saved-enclosure premise.

Reflecting the right owner and rotating the top owner back to the original
packing puts **both actual centers** in `[9/4,59/20]^2`. Their squared
distance is at most

    2(59/20-9/4)^2 = 49/50 < 1.

The already established original-packing center separation says that their
squared distance is strictly greater than one. Hence the two inward extras
cannot coexist. This is a joint contradiction for actual disjoint squares,
not the conjunction of two independently saved pose domains.

The original pruned domains force exactly one complete vector when both
extras occur:

    [{2,12},{0,10},empty,empty,empty,{4,13},{8,18},{3,14},
     {1,11},{6,15},{9,16,19},{5,7,17}].

`C977OppositeWallExtras` supplies ordinary kernel checks of membership,
uniqueness, and the resulting count56, together with original-packing
`actual_not_excluded` and `canonical_remaining_cover`. These statements have
been assembled in source; this worker has not compiled them.

## Central wing propagation from an actual foreign segment

There is a further uniform joint implication, now in
`Compact/Geometry/CentralWingReach.lean`. In its generic coordinates, the
wing Q owns strict points

    p=(1.65,1.65), d=(2,2.26), w=(1,1.74),

misses `t=(1.65,2.35)`, and is disjoint from a foreign square A containing
the closed segment from `e=(2,1.74)` to `m=(2.26,2)`. Its side satisfies
`1<a<=1.001`. Then Q strictly contains `(1,1.5)`, hence also `(1,1.6)`
by interpolation with w.

Reindex its faces so `c>0` and `|s|<=c`, preserving the physical square.
For `0<=s<=c/2`, `CentralSegmentAngle.exclude_small_nonnegative` finds a
point of the actual foreign segment strictly inside Q. For `c/2<=s<=c`,
the unit normal implies `c>=7/10` and `c+s>=4/3`: the latter follows from
`(2s-c)(2c-s)>=0`, hence `5cs>=2`. The owned difference `d-w` would require

    a > c+(13/25)s
      = (13/25)(c+s)+(12/25)c
      >= 386/375 > 1001/1000,

contradicting the original normalization cap. Thus `s<0`.

In this remaining sector, w, d, and p respectively rule out t's lower U,
upper U, and lower V escape, so t lies on or above Q's upper V face.
The target's U bounds follow from w and p, and its upper V bound from w.
The initial lower V argument used `t-(1,1.6)=(13/20,3/4)`, with squared
norm `197/200<1<a^2`. The source now proves the stronger target `(1,1.5)`:
the upper-V escape of t and strict d imply `9c+35s>0`, and

    400[1-((17/20)c-(13/20)s)^2]
      = 12c(9c+35s)+(c+11s)^2+2c^2+110s^2 >= 0.

Thus the V displacement from `(1,1.5)` to t is at most one. The side is
strictly greater than one, so all target inequalities remain strict.

For the original right central owner6, reflect x. Its marker9 supplies p,
optional auxiliary5 supplies d, forced auxiliary8 supplies w, and globally
unused marker10 supplies t. The foreign owner5 has forced auxiliaries4
and13, supplying the two segment endpoints. Therefore

    5 in owner6 => 18 in owner6.

For owner7 use the square-level transformation `(x,y)->(y,4-x)`. Its
marker11, optional16, forced14, and unused marker10 give the same premises;
the same actual owner5 supplies the segment. Therefore

    16 in owner7 => 3 in owner7.

The same adapters export the strict points `(3,1.5)` in owner6 under its
extra5, and `(1.5,3)` in owner7 under its extra16. These give a unit
horizontal or vertical span with the inward owned point. They do not by
themselves supply the three foreign slots required for a section-capacity
contradiction.

`Compact/Bridge/C977CentralWingReach.lean` supplies both original-family
adapters and filters by these two implications. A direct domain count gives
two disjoint groups of three removed vectors: owner6's forbidden local set
`{5,8,16}` and owner7's forbidden local set `{5,14,16}`. Neither group
contains the already excluded opposite-wall-extra vector. The new source
contains an ordinary kernel `decide` statement for count50 and preserves
all original canonical facts in its coverage theorem. This worker has not
executed that statement or compiled these modules.
The parent independently ran a bounded exact source-domain enumeration;
`evidence/c977-fifty-vectors.json` records 57 initial vectors, one opposite
wall exclusion, six wing exclusions, zero overlap, and 50 remaining. This
checks the combinatorial count only, not the geometric Lean proofs.

## Next coupled row argument: exact ingredient and unresolved gap

In the owner6 extra5 branch, the same signed-frame derivation gives a
physical frame `(c,s)` with `c>0` and `0<s<(9/35)c`. At the physical line
`y=2`, its strict owned points `(2,2.26)` and `(3,1.74)` force the two V
face intersections respectively below `89/90` and above `361/90`:

    (2c-(V+a))/s < 2-(13/50)c/s < 89/90,
    (2c-V)/s > 3+(13/50)c/s > 361/90.

The foreign owner5 strictly owns `(1.74,2)`, while owner6 strictly owns
`(2.26,2)`. Since the V interval contains `[1,4]`, disjointness forces the
owner6 U-left row endpoint to be at least1.74. Container containment forces
its U-right endpoint to be at most4. Consequently its complete U interval
is a horizontal section at `y=2`, of length `a/c>1`. This uses an actual
foreign owned point, the full square, and the container, rather than a
saved section enclosure. No additional Lean module was added for this
ingredient alone.

The row also meets owner8 at `(.914,2)`, owner5 at `(1.74,2)`, and owner10
at `(3.086,2)`. These three foreign abscissae do not yield a capacity
contradiction by themselves: their gaps can exceed one. The wall squares
can individually have short sections on this row even with all their
currently established forced and missing points. Their disjoint corner
neighbors' full square geometry is needed to control those deficits.

A proposed entrance through virtual lower and left walls at1 for owner5
is now disproved as a local implication. `audit/C977-SINGLETON-WALLS.md`
gives exact rational full squares with the original local ownership,
strengthened singleton anchors, containment and disjointness, yet the
central square has strict interior points below1. Transposition also
defeats the proposed left wall. The actual tilted-face alternatives are
retained in `Compact/Geometry/C977SingletonSeparation.lean`, with explicit
sector hypotheses and no all-vector coverage claim. The counterexample
still contains `(2,2)`. The complete source theorem
`C977NegativeCorner.point` forces that point from the original bottom
singleton shape and actual foreign left-singleton segment when the bottom
and central squares both have negative canonical frames. It needs only
the original singleton anchors, no strengthened point or side upper cap.
The all-angle `C977CentralReach.central_points` additionally derives strict
owner5 points `(2,1.5)` and `(1.5,2)` from original ownership and singleton
segments. These support the complementary bottom-sign theorem and its
transpose. Consequently `C977CornerReach.central_point_or_positive_corner`
now reduces the original bottom-missing-corner entrance to either owner5
owning `(2,2)`, or a strictly positive central frame with owner1 owning
`(1,1)`. The latter remains open. The central-point result itself still
needs a complete C977 ending. `audit/C977-NEGATIVE-CORNER-COUPLING.md`
gives the exact arguments and coverage boundary. No additional whole
vector has been excluded, and these new sources have not been compiled.

## What remains

The latest `C977CentralWingReach.canonical_remaining_cover` gives source-level
coverage after the wall cuts, one coupled wall exclusion, and both shared
central implications. The remaining50 complete original-vector
contradictions remain unsupplied. The older
`excludes_case_of_single_wall_contexts` interface remains available but is
weaker, asking for all57. No conditional assembly is an unconditional case
exclusion.

The research plan's sign4/sign8/sign12 traces (53,28,30 selectors) are now
mathematically unnecessary once this source is accepted. The sign0 shared
758-selector prefix and the six exceptional vector routes are not replaced
by the present argument. There is no new enclosure or ancestry assertion.

The initial weaker wall-cut idea was to force inward auxiliary ownership under a low
opposite-wall center. The globally unused central marker removes that
alternative entirely. The weaker filtering construction was discarded from
source, so there is no additional count to combine with the current result.
