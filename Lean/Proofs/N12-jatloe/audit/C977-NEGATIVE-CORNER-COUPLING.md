# A whole continuous corner sector forces the central point

Mathematical source audit, 11 October 2026. This argument uses actual full
squares and an actual foreign owned segment. A complete source theorem is
now written as `C977NegativeCorner.point`, with scalar helpers in
`C977CornerCubic`, `C977CornerHalfAngle`, `C977CornerSectorBounds`, and
`C977CornerSupportBounds`. These sources have not been compiled. No numerical
search or saved pose enclosure is used.

## Statement and exact coverage boundary

Let O and A be disjoint congruent open squares of side `a>1`, with signed
canonical frames `(c,-t)` and `(C,-T)`, respectively, where

    0<=t<=c, c^2+t^2=1, 0<=T<=C, C^2+T^2=1.

Assume O is above the container's bottom wall, misses `(1,1)`, and owns
its marker `(1,.914)`, original near anchor `(1.12,1)`, and original lower
anchor `(1.87,.76)`. Assume A owns `(1.65,1.65)`, `(2,1.74)`, `(1.74,2)`.
Finally assume A is disjoint from a foreign square owning both
`(1,1.12)` and `(1,1.74)`. Then A strictly owns `(2,2)`.

The C977 singleton owners and southwest central owner have every point,
containment, congruence and disjointness premise. The displayed theorem
itself retains both negative-sector hypotheses. Further source work now
covers either bottom-singleton sign and the transposed sector, as detailed
below. This still does not exclude an entire representative or another
whole ownership vector.

## Original-family orientation entrance

`SouthwestCentralReach` derives strict central points `(2,1.5)` and
`(1.5,2)` with no orientation restriction. Its northeast form is exactly
`FourSquareANarrow.point_of_higher_R` after positive face reindexing; the
southwest form is its half-turn. The required two excluded left points
`(1,1.5)` and `(1,1.6)` are strict points on the actual left singleton's
original segment between heights `1.12` and `1.74`. Transposition gives
the second result from the bottom singleton's original horizontal segment.
The other missing premises are precisely the southwest square's absence
from the three other central markers.

`C977CentralReach.central_points` binds these implications to original
ordered owner5. It assumes only the original normalized packing and C977
family. Marker8 and forced auxiliary points4 and13 supply its triangle;
its exact marker code excludes9,10,11. It chooses no missing-corner root,
wall branch, orientation, or ownership vector.

Kernel's `C696PositiveCorner.point` uses the new strict point `(1.5,2)` to
complete the positive-bottom/negative-central sector, with the original
lower singleton anchor `(1.87,.76)`. `SouthwestNegativeCorner.point`
therefore covers all bottom-singleton orientations for a negative central
frame. `SouthwestCornerTranspose.point` covers a positive central frame
when the left singleton misses `(1,1)`, by transposing actual full squares.

The original-family theorem
`C977CornerReach.central_point_or_positive_corner` now proves, assuming
the bottom singleton misses `(1,1)`, the precise alternative:

    owner5 strictly owns (2,2), or
    owner5 has a strictly positive canonical frame and owner1 owns (1,1).

All frame changes preserve exact interiors and side lengths. The remaining
positive-central/left-corner-present branch is still open. Even obtaining
the central point in all orientations would still need to be connected to
the complete C977 ending. All newly listed sources are uncompiled; no
additional whole-vector exclusion or completed global theorem is claimed.

### The positive residual genuinely needs another original owner

Parent's exact rational diagnostic
`evidence/three-corner-positive-exact-aux-countermodel.json` satisfies the
full local O/L/A geometry, their exact original marker and auxiliary
signatures, the five strict A points, containment, congruence, and all three
actual pair separations, while A misses `(2,2)`. Thus a universal
three-square completion of the positive residual is false. This does not
affect either completed negative-central sector or the stated residual
cover above.

The actual left-wall owner8 strictly owns both `(.914,2)` and `(1,2.26)`.
Their segment excludes that first diagnostic: its point
`(2457/2500,276/125)`, at parameter4/5, lies strictly in the diagnostic A.
However the parent's subsequent bounded exact falsification found13 local
models avoiding the entire foreign segment, recorded in
`evidence/three-corner-segment-diagnostic.json`. That segment is therefore
also insufficient for a universal center theorem. The complete actual
wall square, its left containment, and its disjointness from L and A remain
necessary candidate inputs.

Four reusable source reductions survive these counterexamples:

- `CornerSingletonPair.alternatives` uses L's owned corner to leave one
  directed O/L separator per square frame. A positive frame can separate
  only with O below L transversely; a negative frame can separate only
  with L to the left of O longitudinally. No canonical angle cap is needed
  for this reduction beyond a positive cosine component.
- `PositiveCentralTransverse.alternatives` assumes A's positive canonical
  frame and its missing-center upper-U cap, and uses its two new strict
  crosspoints to exclude both O/A longitudinal axes for either canonical
  sign of O. Only the two forward transverse alternatives remain. The
  source includes exact continuous scalar margins and support identities.
- `CentralLeftWallSeparation.alternatives` conditionally assumes A owns
  `(1,2)`. In any positive face frames `(C,S)` and `(d,t)`, the actual wall
  marker and point `(1,2.26)` rule out both longitudinal axes and reverse
  transverse directions. The two possibilities are
  `A.hiV<=lower(W,(-S,C))` or `upper(A,(-t,d))<=W.loV`.
  The point `(1,2)` is a separate unresolved intermediate at this checkpoint;
  this theorem does not silently supply it.
- `LeftSingletonWallSeparation.guarded_alternatives` retains all four
  possible forward L/W axes in arbitrary positive frames. Reverse axes
  are excluded by the original markers `(.914,1)` and `(.914,2)`.
  Separation on L's U axis necessarily has `L.s>L.c/4`, by the actual
  left wall, full side length greater than1, and far seed `(.76,1.87)`.
  Separation on W's U axis necessarily has `W.s>.086W.c`, using L's
  owned corner and W's marker. No such angle guard is imposed on the
  two forward V axes. In particular this reduction does not discard
  longitudinal modes for steep positive frames.

These are actual support restrictions, not universal positive-sector
closures. They have not been compiled. No remaining-vector count changes.

The negative-wall sector now has a stronger continuous reduction in
`CentralLeftWallNegative.wall_axis`. Conditional on A's explicit point
`(1,2)`, its actual point `(2,1.5)` and original side cap imply
`S<.8C`: their V-coordinate difference is `S+.5C`, and a slope at least
`.8` would make that difference exceed1.001. The actual W top-marker and
foreign L far-point exclusions give `t<.6` by
`LeftWallNegativeFaces.lower_face_and_tilt`. Write W's negative frame as
`(d,-t)`. To exclude the A-axis separator, the actual W left wall and
upper-V cap reduce exactly to

    (1-d)(C-Sd)+Ct(d-.914)>=0.

For `d>=.914` the sign is immediate. Otherwise use `S<=.8C`, `t<=.6`,
and the exact identity

    (1-d)(1-.8d)+.6(d-.914)=.8(d-.75)^2+.0016.

Thus every negative-canonical W has the single surviving directed
separator `W.hiU<=lower(A,(d,-t))`. Zero wall tilt is included in the
direct signed SAT reduction; no division by t occurs. This is a full
support transition used by the four-square argument, with the unfinished
central point `(1,2)` hypothesis still explicit. It does not exclude a
whole representative or prove the positive-central completion.

## Forced bands and actual separating axes

Write the lower bands of O as `u,v`, and those of A as `U,V`. The corner
is already between O's two V faces and below its upper U face, by the
marker and near/lower anchors; therefore missing the corner forces

    u>=c-t.

The bottom wall gives `cv>=t(u+a)`. Consequently

    v+a >= a+(t/c)(a+c-t) > B,
    B=1+t+t(1-t)/c.

All denominators are positive: `c,C>=1/sqrt(2)`. The strict inequality
uses `a>1`; the orientation axes themselves may occur at zero tilt.

For A, the cross points supply three strict bands of `(2,2)`. Its only
possible escape is the upper V face. Suppose for contradiction that

    V+a<=2(C+T).                                  (S)

The zero-tilt case `T=0` is immediately impossible by the strict point
`(1.74,2)`, so assume `T>0`. The full-square SAT reduction in
`Compact/Geometry/C977SingletonSeparation.lean` leaves precisely

    v+a <= lower(A,(t,c)),                         (O-axis)
    upper(O,(T,C)) <= V.                           (A-axis)

These are inequalities for the full supports, not independent face choices
or previously saved square domains. Set

    delta=cT-tC, K=cC+tT.

## The A-axis alternative is impossible

Parameterize the nonnegative tilt angles by `alpha` for O and `beta` for A.
This is only a continuous algebraic parameterization of unit normals.

If `beta>=alpha`, then `delta>=0`, and the corner and bottom wall give

    upper(O,(T,C)) >= (T/c)(c-t+a)+Ka.

Adding `a` and replacing `a>1`, the difference from `2(C+T)` is strictly
larger than

    (1-C)-(1-c)[C-T(1-t)/c] >= 0.

Indeed `C<=c`, so `1-C>=1-c`, and the bracket is at most `C<=1`.
This contradicts the A-axis alternative and (S).

If `beta<=alpha`, the lower bound is instead

    upper(O,(T,C)) >= (T/c)(c-t)+Ka(1+t/c).

After adding `a` and replacing it by one, the difference becomes

    1-A0*C-B0*T,
    A0=2-c-t, B0=(1-t)(c+t)/c.

Its maximum is at equal normals. The source avoids angular monotonicity:
for any nonnegative coefficient A0 and `A0*t<=B0*c`, the identity

    c[(A0*c+B0*t)-(A0*C+B0*T)]
      = A0[1-(cC+tT)]+(B0*c-A0*t)(t-T)>=0

uses only `cC+tT<=1` and `T<=t`. Here
`B0*c-A0*t=c-t>=0`. At equal normals the displayed difference equals

    (1-c)(t-(1-c))/c >=0,

using `c+t>=1`. Strict `a>1` again makes the actual difference positive.

## The O-axis alternative forces beta>alpha

Suppose `beta<=alpha`, so `delta<=0`. The strict cross point `(1.74,2)`
gives `U<1.74C-2T`. With (S), the minimum support of A on `(t,c)` is
strictly smaller than

    F(beta)=c[2+.26CT-C]+t[1.74+.26T^2-T].

The source now bounds this function by its endpoint values through an exact
algebraic chord. Set `k=.26` and `G=(1-kT)(cC+tT)`, so
`F=2c+1.74t-G`. Then

    tG-[(t-T)c+T(1-kt)]
      = c[t(C-1)+T(1-c)]+ktT[1-(cC+tT)]>=0.

The second term is nonnegative. For the first, use

    t(C-1)+T(1-c)
      =tT[t/(1+c)-T/(1+C)]>=0,

since `T<=t` implies `c<=C`. Thus this is a weighted endpoint bound;
the case `t=0` is immediate. Both endpoint values are at most B. At
`beta=alpha`, this is

    F(alpha)=2(c+t)-1 <= B,
    c[B-F(alpha)]=(1-c)(t-(1-c))>=0.

At `beta=0`, it is `F(0)=c+1.74t<=B`. For the latter estimate, use

    .26c(1+c) >= .26(.7)(1.7) > 1/4 >= t(1-t),
    c[B-c-1.74t]=t[.26c-t(1-t)/(1+c)]>=0.

The exact chord bounds F by its endpoint maximum, contradicting O-axis
separation and `v+a>B`. We have therefore reduced to

    delta>0, beta>alpha,
    -delta(U+a)+KV >= v+a > B.                    (R)

Only one actual separating direction survives.

## One exact cubic comparison handles the final sector

Use rational half-angle coordinates

    r=(1-t)/c, rho=(1-T)/C, 0<rho<=r<=1,
    c=2r/(1+r^2), t=(1-r^2)/(1+r^2),
    B=(2+r-r^3)/(1+r^2).

To prove `B>=c*f+t*g`, it suffices to prove

    H(r)=(2-g)+(1-2f)r+gr^2-r^3>=0.

For fixed `rho,f,g`, the exact identity is

    H(r)=[(1-r)H(rho)+(r-rho)H(1)]/(1-rho)
         +(r-rho)(1-r)(r+1+rho-g).                (I)

Here `rho<1`, since `T>0`.

First, (R) and (S) force `CU+TV<1`, the minimum x-coordinate of A. If
instead `CU+TV>=1`, their combination and `a>1` contradict the comparison
with

    f=2+(T-1)/C-T, g=1+C.

For these choices, `f<=1`, `H(1)>=0`, and `H(rho)>=0` is exactly the
equal-angle inequality `B>=2(C+T)-1` already proved. The final factor in
(I) is nonnegative because

    r+1+rho-g >= 2rho-C = (1-T)^2/C >=0.

Second, (R) and (S) force `U<C-1.12T`. Otherwise they contradict the
same comparison with

    f=2-.88T^2+CT-C-T,
    g=1+T^2+.88CT+C-T.

Again the equal-angle endpoint is `H(rho)>=0`. Also `f<=1` and `g<=2`.
The latter inequality is close enough that its exact certificate is useful.
Put `z=C-.9`. The identity

    P(C)=625-475C-1241C^2+1109C^3
        =1109(C-.7)z^2+835z^2
          +(1393/20000)(100z-1)^2+13627/20000

proves `P(C)>0`, since `C>=.7`. Now

    [T(1-.88C)]^2-[C(1-C)]^2=(1-C)P(C)/625>=0.

Both bracketed terms are nonnegative, so `T(1-.88C)>=C(1-C)`, which is
exactly `g<=2`.

For `T<=3/5`, one has `rho>=1/2`; therefore the final factor in (I)
is at least `2rho-1>=0`, proving H nonnegative.

For `T>=3/5`, use `1-C<=3T^2/5`, a consequence of `C>=2/3`, to obtain

    f<=1-(7/25+(3/5)T)T^2<=481/625<4/5.

Also `rho>=2/5`: indeed `.4C+T<=.7(C+T)<=1`. Thus `r>=2/5`, and
using `g<=2` directly in H yields

    H(r)>=r[1-2f+2r-r^2]>=r[-3/5+16/25]=r/25>0.

This completes both needed comparisons throughout the continuous sector.

## The foreign segment gives the contradiction

At x=1, the two lower face inequalities of A are

    y>(V-T)/C, y<(C-U)/T.

The established `CU+TV<1` says these endpoints are strictly ordered.
The bound `U<C-1.12T` says the upper endpoint exceeds1.12. Finally (S)
and `a>1` give the lower endpoint below1.74, since

    T+.26C <= .63(C+T) <= .9 < 1.

Therefore the open section intersects `[1.12,1.74]`. Every point of this
vertical segment satisfies A's strict upper face inequalities, using its
cross points `(2,1.74)` and `(1.74,2)`. The foreign singleton owns the
entire closed segment strictly, by convexity from its strict endpoints.
This is a point in both actual interiors, contradicting disjointness.

Thus A strictly owns `(2,2)` in the stated negative/negative frame sector.
The proof keeps all equality cases at the separating faces and obtains
strictness from owned points and `a>1`.
