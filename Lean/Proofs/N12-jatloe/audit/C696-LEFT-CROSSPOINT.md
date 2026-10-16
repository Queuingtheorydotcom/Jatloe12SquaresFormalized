# The three-square left-crosspoint implication is false

**Entrance correction (2026-10-11):** the conditional wall arguments below
use `W` missing `(1,2.88)`, which has not been derived for C696/C977. Their
northwest corner owner has paired marker mask 192, not the singleton whose
extra seed gives that point. See `POSITIVE-CENTRAL-SIGN-MATRIX.md` for the
complete sign/ownership matrix and the precise remaining original-premise
gap. The generic geometric implications remain conditional on their
stated hypotheses; they do not close an original packing cell yet.

The proposed intermediate was: if the positive canonical central square A
misses `(2,2)`, then the actual bottom and left singletons force it to
strictly own `(1,2)`. The parent's exact rational check has now refuted this
three-square statement, including the full original marker and auxiliary
signatures. A valid replacement must use the actual wall square W as well.
`PositiveCentralLeftBand.lean` supplies the following valid consequences:

* Missing `(1,2)` means `hiV ≤ 2C−S`; the other three target bands follow
  from the center U-cap, side greater than one, the central marker and the
  strict point `(1.5,2)`.
* Independently of either escape, the original absent northwest marker,
  both strict crosspoints `(1.5,2)` and `(2,1.5)`, and the actual foreign
  point `(1,1.6)` imply `hiV ≤ 2.35C−1.65S`. Otherwise the U-width is at
  most `.65C+.75S<1`, contradicting the side. The strict norm bound is
  `.65²+.75²=.985`. If the desired left point is later proved, this face
  bound immediately gives the strict angular restriction `13S<7C`.

## The remaining separator is now unique

The new source modules `PositiveCentralNegativeBottom.lean` and
`PositiveCentralPositiveBottom.lean` eliminate separation on A's transverse
axis under the left-point escape. They use the actual bottom wall and
original marker or upper-U face, not a numerical enclosure. For a negative
bottom frame `(c,-t)`, the coefficient comparison is

    c(2−c−t)C + t(c+t−.914)S ≤ c.

For `t≤.45` the two nonnegative coefficients sum to at most `c`. For
`t≥.45` they are bounded by `.85c` and `.52c`, with squared norm `.9929<1`.
The positive-bottom proof uses monotonicity on one relative-angle cone and
the existing exact `linear_arc_max` theorem on the other.

`PositiveCentralTransverse.only_bottom_axis` now applies these inequalities
to the original O/A premises. If A misses `(1,2)`, the only remaining
separation is

    O.hiV ≤ lower A (−O.s,O.c).

If O's canonical sine is nonnegative, `own_axis_angle` further gives
`O.s<A.s`. The scalar proof uses the existing exact sine-coordinate chord
identity with coefficient `1/2`, whose endpoints are nonnegative. If O's
sine is negative, it is already strictly below A's nonnegative sine.

These source proofs are not yet replayed. They do not prove the left point:
the remaining own-O separator is compatible with all three full O/L/A
squares. The actual fourth wall square, with its original foreign points,
is needed for the next proposed implication.

## Exact counterexample with all three original local squares

The parent independently checked the following construction in
`evidence/positive-central-three-square-left-point-countermodel.json`.
The receipt records `full_local_claim_refuted=true`. All three complete
squares are contained, congruent, have their exact original marker and
auxiliary signatures, satisfy the original extra singleton seeds, and are
pairwise disjoint. L owns `(1,1)`, O misses it, and A misses both `(2,2)`
and `(1,2)`.

    a = 100000001/100000000
    p = 39999/40001, q = 400/40001
    O.c = p, O.s = -q
    O.loU = 2*p - (457/500)*q - a
    O.loV = (q/p)*(O.loU+a)

    L.c = 1, L.s = 0
    L.loU = 0, L.loV = 23/25

    C = 1591/1609, S = 240/1609
    A.c = C, A.s = S
    A.loU = 2*(C+S)-a
    A.loV = 2*C-S-a

The separating axes are O.U for O/L, A.U for L/A, and O.V for O/A.
This is a local counterexample, not a twelve-square packing. In particular
it does not place W, whose genuine strict points include `(.914,2)`,
`(1,2.26)`, `(1,2.4)`, and whose genuine excluded points include L's far
seed `(.76,1.87)` and the upper marker `(.914,3)`. The stronger exclusion
of `(1,2.88)` used later is an additional unproved entrance obligation,
not an original paired-corner seed.

## Exact counterexample against an O/A-only version

The following exact rational construction passed the parent's independent
fraction check. Its complete receipt is
`evidence/positive-central-two-square-left-point-countermodel.json`.
This is a two-square counterexample, not a twelve-square packing or a Lean
replay. No numerical job was run by this worker.

    a = 100000001/100000000
    c = 999999/1000001
    t = 2000/1000001
    O.c = c, O.s = −t
    O.loU = c−t+1/100000
    O.loV = (t/c)*(O.loU+a)

    C = 399/401, S = 40/401
    A.c = C, A.s = S
    A.loU = 2*(C+S)−a
    A.loV = 2*C−S−a

O's bottom wall is an equality. Its corner `(1,1)` is below its lower U
face. A misses `(2,2)` on its upper U face and `(1,2)` on its upper V face.
The original O and A strict points, exact marker and auxiliary signatures,
container containment and full-square disjointness all passed that check.
The full third square L has **not** been placed.

Writing `D=t*C+c*S` and `K=c*C−t*S`, the verified O/A separation is

    O.loV+a < D*A.loU+K*A.loV.

The right side is approximately `1.00667`; the left is approximately
`1.003996`. These approximations are explanatory, not acceptance evidence.
Thus an O/A-only implication is false. The remaining proof must use the
actual third square L, or still more of the original packing. The later
three-square counterexample above resolves that distinction: L alone is
insufficient as well.

## Valid negative-bottom replacement and one completed wall branch

The new source route does not reuse the false three-square point contract.
`PositiveCentralNegativeFloor.actual` instead proves the true horizontal
lower support of A is strictly above `y=1`, from the original negative O
corner face, the actual O/A separator and A's center upper-U escape. The
continuous scalar estimate is

    boundary(c,t) >= c + 1.6*t,
    S + .4*C <= 1.

The first follows from `c+t-1 >= .8*c*t`. This genuine floor also proves
A strictly owns `(1.2,2)` and that its leftmost support is strictly less
than `1`. Neither consequence asserts that A owns any specified point
on `x=1`.

For a positive canonical W, `PositiveWallEscapeFaces.faces` uses the
actual excluded seeds `F=(.76,1.87)` and `H=(1,2.88)`. The lower-U escape
of F is impossible: paired with H's upper-U escape it gives width below
one, and paired with H's upper-V escape it forces W to own the same
`(1.2,2)` as A. Thus W must satisfy

    W.loV >= 1.87*d - .76*s.

Every wall orientation remains represented in the two alternatives:

* `W.hiU <= d+2.88*s` and `s<.6`;
* `W.hiV <= 2.88*d-s` and `s<1/24`.

`PositiveWallUpperVImpossible.impossible` closes the second alternative
using complete actual squares. W strictly owns `(1,1.88)` and `(1,2.4)`.
A's floor, center cap and genuine absent-northwest-marker cap imply only
that its upper-V exit on `x=1` is above `1.88`. The exact estimate uses
`(C+S)*(1-.35*C)<1`, then `C>.81` and `C*S<=.476`. It does **not** claim
the false fixed point `A.Inside 1 1.88`: the verified counterexample's
lower-U entry is higher than `1.88`. Applying the existing increasing-
segment avoidance theorem to W's strict vertical segment gives either
the wrong V-exit bound or `xminA>=1`, contradicting the genuine support
bound. This closes the entire upper-V wall branch at a variable height.

## Completed positive-L sector of the remaining upper-U branch

`PositiveWallTransverse.alternatives` first removes both longitudinal
A/W axes: the actual closed northwest corner of A has `x<1` and
`y<=2.35`, whereas W strictly owns `(1,2.4)`. Only the two upward V axes
remain. This reduction keeps the full supports of both squares.

For the missing-left branch, `PositiveCornerSmallBottom.tilt` derives
`0<t<.2` for the negative bottom singleton. A's two actual upper-face
caps give the exact scalar upper bound

    boundary(c,t) < c*(2+C*S-C-S) + t*(2-S^2-C+S).

The coefficient bounds are `1.08` and `1.5`. The competing lower-bound
gap at `t=.2` is exactly `1/625`, and the quadratic chord stays positive
on the whole remaining canonical interval. With this small angle, the
actual missing bottom marker forces `O.hiU<=2*c-.914*t`.

`PositiveWallUpperUPositiveLeft.impossible` now handles every O/L and
L/W separator when L has a positive canonical frame. Its own V axis
cannot separate L from the full negative O, so O's U axis is forced.
The true left wall and this separator imply `L.hiV>1.914*l`. That face
bound rules out both L axes against W. W's U axis is ruled out by the
actual L far seed and W's upper-U cap. Its V axis is ruled out by a
second complete-support identity whose continuous remainder is

    ((c+t)/2)*(r-2*(1-l)) + ((c-3*t)/2)*r + (1-c) >= 0.

Every term is nonnegative on the actual small-bottom and canonical-L
sectors. The final wall scalar is

    (1-d)*(d+s) + .034*d*s >= 0.

`PositiveWallPositiveLeft.missing_left_impossible` binds these two wall
branches to the original O/L/A/W point, containment, common-side and
pairwise-disjointness premises. It derives every intermediate face cut;
it does not assume the disputed point or any saved numerical ancestry.

The negative-L complement and the other signed wall/central sectors
remain separate obligations. No full C696 or C977 case is claimed. All
new Lean sources in this note await the final assembled replay.
