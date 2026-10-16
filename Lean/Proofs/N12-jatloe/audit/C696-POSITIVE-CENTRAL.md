# Remaining positive-central corner sector

Source-only mathematical checkpoint, 11 October 2026. No compiler,
numerical search, or saved pose enclosure was used. The full sector remains
unproved. `SouthwestNegativeCorner.point` covers a negative canonical
central square for either bottom-singleton orientation. Coordinate
transposition covers positive central orientation if the left singleton
also misses `(1,1)`. Thus the genuinely remaining case has the left
singleton strictly owning `(1,1)`.

The actual local data include congruent squares O, L, A of side `a>1`,
container containment, pairwise interior disjointness, exact marker masks,
all original singleton seeds, and both newly proved central crosspoints.
Only A is required to have a positive canonical frame `(C,S)` in this
remaining sector. Missing `(2,2)` then forces

    A.loU + a <= 2(C+S).

## Why replacing O by its finitely many owned points is insufficient

There is an exact two-square example satisfying even the natural extra
exclusions of O's original points from L. Its role is diagnostic only: it
does not give three disjoint squares, let alone a twelve-square packing.

Take

    c = 399/401, s = 40/401, a = 10001/10000,
    v = c - (28/25)s = 1771/2005,
    u = (s/c)(v+a) = 7552401/39999750.

Give L the positive frame `(c,s)` and lower bands `(u,v)`. Give A the same
frame and lower bands `(2(c+s)-a, 1)`. Both normals have unit norm, since
`399^2+40^2=401^2`.

The leftmost coordinate of L is exactly zero:

    c*u-s*(v+a)=0.

Both squares are contained in `[0,4]^2`. They are strictly separated on
their common U axis because

    A.loU - (L.loU+a) = 823962/1599990000 > 0.

L strictly owns `(1,1)`, its marker `(.914,1)`, and its original seeds
`(1,1.12)`, `(1,1.74)`, `(.76,1.87)`. A strictly owns all five required
points `(1.65,1.65)`, `(2,1.74)`, `(1.74,2)`, `(2,1.5)`, `(1.5,2)`.
A misses `(2,2)` exactly on its upper U face and excludes the other three
central markers. L excludes the next left marker `(.914,2)` on the upper
V side.

Moreover all four actual O-owned points are excluded from L:

* `(1.12,1)` lies exactly on L's lower V face by the definition of v.
* `(1,.914)` lies below it, since `.086c-.12s>0`.
* `(1.74,1)` lies below it, since `s>0`.
* `(1.87,.76)` lies below it, since `.24c+.75s>0`.

These checks are rational substitutions into the displayed bands, not
numerical optimization. The gap between the two U intervals can also be
read continuously: at unit side it is

    s^2*(28/25-(22/25)c-s)/(c*(1+c)),

and increasing the common side from 1 to a subtracts
`(2+s/c)(a-1)`. At the displayed exact normal the result remains positive.

Therefore a proof must retain more geometry of O than exclusion of its
named seed points from L. In particular, the actual square's bottom-wall
constraint and one genuine O/L separating face cannot be replaced by a
foreign finite set.

## Useful remaining reduction

For O/L separation with L owning `(1,1)`, the canonical signs dictate
which face can separate. On any positive canonical frame `(c,s)`, the
U projections overlap, and only the V direction can separate, with O
below L. On any negative canonical frame `(c,-t)`, the V projections
overlap, and only the U direction can separate, with L left of O.
This follows from strict projections of the actual corner, marker, and
singleton seed points. The corresponding source reduction is being
developed separately; this note does not assert a completed Lean proof.

## Candidate obstruction to the full three-square statement

A stronger exact construction was subsequently found by hand. The parent
checked its rational substitutions independently in
`evidence/three-corner-positive-countermodel.json`: all three squares,
the strict required points, exact marker masks, containment, and actual
pairwise separation passed. There is one extra original auxiliary point
inside A, however, so the first version below only refutes the weaker
marker-and-five-point contract.

Let

    a=10001/10000, m=457/500,
    co=12/13, so=5/13,
    c=399/401, s=40/401,
    K=co*c+so*s=4988/5213,
    D=so*c-co*s=1515/5213.

Use frame `(co,so)` for O and `(c,s)` for both L and A. Choose the bands

    Ou=2co+m*so-a,
    Ov=-(so/co)*Ou,
    Lu=(s/co)*(Ov+a+a*(K+D)),
    Lv=(c/s)*Lu-a,
    Au=2(c+s)-a,
    Av=(47/20)c-(33/20)s-a.

The O bottom wall and L left wall are equalities. O/L are separated along
O's V normal, also at equality:

    Ov+a = -D*(Lu+a)+K*Lv.

L/A are separated along their common U normal if `Lu+a<Au`; the hand
evaluation gives a positive gap about `.0003576`. O/A are separated along
A's V normal if

    D*(Ou+a)+K*(Ov+a) < Av;

the exact gap is `4333831/78195000`. The exact L/A gap is
`10350379/28944180000`.

O's absent next bottom marker is on its upper U face. A's absent `(2,2)`
is on its upper U face, and A's absent northwest central marker is on its
upper V face. All required owned points appear strictly within the
remaining bands, including both new A crosspoints and L's corner. Both
normals are exact rational unit normals. The construction therefore uses
no approximate rotations and no numerical search.

The parent check found the auxiliary ownership of A to be `{1,4,13}`,
where the original local owner has `{4,13}`. Specifically A contains the
foreign point `(1,2.26)` in this first construction. This extra ownership
must not be silently dropped from the original-packing premises.

A hand-derived repair changes only A's lower V band to

    Av=(113/50)c-s-a.

This puts `(1,2.26)` on A's upper V face. The O/A separating gap decreases
by `(9/100)c-(13/20)s`, remaining positive (about `.0307`); the L/A and O/L
separations are unchanged. Both new central crosspoints remain strictly
owned. The symmetric foreign point `(2.26,1)` was already excluded on the
upper U side. The parent independently verified this repaired example in
`evidence/three-corner-positive-exact-aux-countermodel.json`. Its exact
marker masks are `{0}`, `{1}`, `{8}`, and its exact auxiliary masks are
the original `{2,12}`, `{0,10}`, `{4,13}`. All containment, congruence,
strict seed ownership, and full pairwise separation checks pass. Therefore
the strengthened three-square contract is false too. These are exact
rational diagnostics, not Lean replay, and not a twelve-square packing.

## The actual left-wall owner supplies missing geometry

The actual left-wall owner W strictly owns both

    M=(457/500,2), F=(1,113/50).

Its strictly owned segment already intersects the repaired example. For
instance, the parameter `4/5` point on M--F is
`(2457/2500,276/125)`. Thus retaining an actual W/A nonintersection
premise removes the exhibited construction, without needing W's angle.

For a positive central frame `(C,S)`, define

    du=(43/500)C+(13/50)S,
    dv=(13/50)C-(43/500)S.

Both are positive on the canonical arc. Along M--F both U and V increase.
The two new central crosspoints ensure A's upper U face lies beyond all
of the segment and its lower V face lies below all of the segment. The
missing-center cap and `a>1` also imply `A.loU<U(F)`. Consequently W/A
disjointness gives the exact dichotomy

    A.hiV <= V(M)

or

    dv*A.loU-du*A.hiV >= 1641/25000.

The second inequality says that A's upper-left vertex `(X,Y)` satisfies
`.26X-.086Y>=.06564`. The first alternative must be retained: without it,
the second inequality alone is not a universal consequence of segment
avoidance. This is a genuine constraint from a foreign owned segment,
not an assumed coordinate wall. A complete continuous contradiction from
the enlarged original-family data is not yet established.

The segment alone is still insufficient. The parent's bounded exact
diagnostic `evidence/three-corner-segment-diagnostic.json` found rational
three-square configurations satisfying the original local marker and
auxiliary masks, all five central points, the actual three pairwise
separations, and disjointness even from the closed M--F segment. This is a
falsification check, not a proof subdivision. Thus a new closure must keep
the full W square and its actual disjointness from L and A. W's original
exclusion of the upper-left marker `(.914,3)` must also remain explicit;
there is no proved reduction permitting it to be dropped.

## Source reduction retained despite the failed relaxation

`Compact/Geometry/PositiveCentralTransverse.lean`, written by the separate
SAT worker, reduces actual O/A disjointness to the two forward transverse
alternatives throughout positive central orientation and either canonical
O sign. It uses the original O near/far seeds, the central points, side
greater than one, and the missing-center upper U cap. Its two longitudinal
axes are eliminated continuously, without angle subdivision. This is a
useful source-only reduction, not a positive-central closure.

`Compact/Geometry/IncreasingSegmentAvoidance.lean` now contains the generic
affine interval-crossing proof and the specialized `left_wall` dichotomy
above, written by the kernel worker. It preserves tangencies and still
does not assert that the segment condition closes this sector.

No positive-central Lean theorem is asserted by this checkpoint.

## Actual negative wall faces and a continuous angle-order branch

`Compact/Geometry/LeftWallNegativeFaces.lean` is new source-only work.
Write the negative canonical wall frame as `(d,-t)`, with `0<=t<=d`,
`d^2+t^2=1`, and put `m=457/500`. Conditional on A owning `(1,2)`,
actual A/W disjointness makes W miss that point. Its original excluded
marker `(m,3)` and its genuine left container wall then give

    W.hiU <= d-2t,
    W.hiV <= mt+3d,
    a(d+t) <= d*W.hiU+t*W.hiV.

The original excluded L seed `(.76,1.87)` forces

    .76t+1.87d <= W.loV.

The other three bands of that seed follow from the preceding caps and
the wall. The only nontrivial scalar margin is

    d+t-1.13dt-.76-.154t^2 > 0.

It follows from `d+t>=1+(14/17)dt`, `dt<=1/2`, and `t^2<=1/2`.
Consequently `a<=1.13d+.154t`, and the tangent inequality
`.8d+.6t<=1` excludes the entire continuous interval `t>=.6`.
The source has not been compiled by this worker.

The SAT worker's `CentralLeftWallNegative.wall_axis` further reduces
actual A/W separation to

    W.hiU <= (Cd-St)*A.loU-(Sd+Ct)*A.hiV.

This uses the strict A point `(1,2)` as a premise. That point remains a
separate unfinished intermediate, not an established universal fact.

Here is a mathematically checked continuous branch of the angle cycle.
Suppose O is positive canonical `(p,q)`, A is `(C,S)`, and their angles
obey `beta<=tau<=alpha`, where `tau` is W's tilt magnitude. Suppose also
that O/A separate on A's transverse axis. Set

    K=pC+qS, D=qC-pS, z=d+t-1.

The actual bottom wall and the original missing next bottom marker give
`O.loU<=2p+mq-a` and `q*O.loU+p*O.loV>=0`. Since `D>=0`,

    p*upper_O(vA)
      >= -S*O.loU+a*p*(D+K)
      >= a*(p+q)*K-2pS-mqS.

Adding A's side and relaxing `a>1` to 1 and `m<1` to 1 yields the strict
lower bound

    A.hiV > 1+C(p+q)+S*(q/p)*(p+q-1)-2S.

On the canonical arc, both `p+q` and `q/p` increase with angle. Therefore
`tau<=alpha` allows replacement of `(p,q)` by `(d,t)` in this lower bound.
Combine this with `A.loU<=2(C+S)-a`, the actual W-axis separation above,
and W's coupled wall/cap inequalities. The resulting necessary condition
is `E>0`, where

    E=(d^2-z)(1+CS)+dt(2-S^2-z)
        -d*((d+t)C+(d-t)S).

But `E<=0` throughout `0<=S<=t<3/5`, `C>=d>=4/5`:

* Put `R=d^2-z`, `B=d^2(1-t)`. Both are nonnegative.
* `H=2B-3Rt=2-8t+t^2+5t^3+3dt` is nonnegative. Indeed
  `H >= 2-(28/5)t+t^2+5t^3 >= (3/5-t)(5/4-t) >= 0`;
  the middle residual is exactly `5(t-1/2)^2(t+1)`.
* Algebra gives `E=-z^2(1+z)/2+Delta`, with
  `Delta=(1-C)[d^2-dtC-RS]+S*z^2/2`.
* Since `C>=d`, `Delta<=g(S)`, where
  `g(S)=S^2(B-RS)/(1+d)+S*z^2/2`. Here `B-RS>=0` follows
  from `H>=0`, so replacing the denominator is legitimate.
* `g(S)<=g(t)`: after factoring `t-S`, use
  `2(t^2+tS+S^2)<=3t(t+S)` and `2B>=3Rt`.
* Thus `E` is at most its endpoint value at `C=d,S=t`, namely
  `(1-d)[1-d-t(2d^2-2d+1)]<=0`. The last sign follows from
  `1-d=t^2/(1+d)<=t/2` and `2d^2-2d+1>=1/2`.

The parent independently checked this scalar sign with a single exact
two-variable polynomial certificate in
`evidence/positive-corner-angle-order-scalar.json`. The human inequalities
above are the intended proof; that diagnostic is not the geometric
closure. This branch excludes `beta<=tau<=alpha` for O/A separation on
A's axis, conditional on the stated full-W premises and A's `(1,2)`.
The other O/A axis, other angle orders, O's negative orientation, and the
L/W cycle remain open. No whole four-square contradiction is asserted.

The common angle reduction has now been extended to the other O/A axis
and written in `Compact/Geometry/PositiveCentralWallAngleOrder.lean`.
Its public `angle_order` concludes `O.s<t` for positive canonical O and
negative canonical W, retaining the actual O/A/W premises and explicit
strict A `(1,2)`. It consumes the separately written
`NegativeWallAngleOrder.angle_order`, which gives `A.s<t` from A/W and
the original northwest/foreign-point exclusions. Thus an assumed
`t<=O.s` lies exactly in the common interval treated above.

For the second O/A axis set `B=(p+q-q*(2p+q))/p`. After relaxing only the
scalar constants to `a=m=1`, the effective lower central face is

    Hown=1+B/K+2D(C+S)/K.

The preceding central-axis value is `HA=1+D*(2p+q)+K*B`, and

    Hown-HA=(D/K)*(2(C+S)-(K*(2p+q)-D*B)) >= 0.

The last sign follows from the explicitly constructed algebraic point
whose coordinates are

    x=p*(2p+q)-q*B
      =2-q*(1-p)-q^2*(1-q)/p <=2,
    y=q*(2p+q)+p*B=p+q<=2.

This point is only used to verify a polynomial bound on the support
formula; no geometric containment premise is replaced by a virtual
wall. The common source lemma `support_obstruction` retains all actual
band and container inequalities for both support alternatives. The
source is frozen for the parent's scheduled checking and has not been
compiled by this worker. A(1,2), negative O, positive W, and the opposite
O/L/W angle restriction remain outstanding parts of the full problem.

## Correction: the three-square west-point implication is false

The parent has now checked the exact original marker and auxiliary
signatures, additional singleton seeds, container constraints, and all
three full-square separations for
`evidence/positive-central-three-square-left-point-countermodel.json`.
It has `full_local_claim_refuted=true`. Thus A(1,2) cannot be deduced
from the three actual O/L/A squares alone. The earlier angle-order
source remains a conditional lemma with A(1,2) explicitly present.
Its final cancellation API was corrected to
`nonpos_of_mul_nonpos_right`; no compilation was performed here.

The conditional L/W longitudinal exclusion was also written in
`Compact/Geometry/LeftSingletonNegativeWallLongitudinal.lean`.
It requires the explicit W exclusion of (1,2), and does not silently
extend to the newly identified missing-A(1,2) branch.

## Conditional upper-point exclusion bounds negative W without A(1,2)

`Compact/Geometry/NegativeWallTopSeed.lean` removes that disputed
premise from a useful pair of face restrictions. Let W=(d,-t) be
negative canonical, A=(C,S) positive canonical, with their actual
common side greater than one and actual disjointness. Retain the
central upper-U cap and actual A points (1.5,2), (2,1.5), (1.65,1.65).
Retain W's marker (.914,2), auxiliary points (1,2.26), (1,2.4), and its
exclusions of (.76,1.87) and (1,2.88). The first exclusion is genuinely
foreign to L. The later original-packing audit below found that the
second exclusion is not supplied by the paired upper-corner owner.
Then

    .76t+1.87d <= W.loV,
    W.hiV <= t+2.88d,
    t < .51.

These statements do not assume A(1,2), W missing (1,2), or a virtual
wall. The actual A/W SAT reduces to the same two support modes

    A.hiV <= lower_W(-S,C),
    W.hiU <= lower_A(d,-t).

The true point W(1,2.4) eliminates the reverse W-V mode that previously
used A(1,2). To prove the upper face, suppose W.loU >= d-2.88t.
Writing k=Cd-St and h=Sd+Ct, the W-U mode contradicts the scalar gap

    1 - d(1-C)^2/2 - t[.88+S(1-C/2)] > 0.

On the entire canonical arc, C>=.7 and S,t<=.71 give a lower bound
.002535. The A-V mode contradicts the nonpositive scalar

    Ct(.88t-.086d-1) + S(.5+.086t^2+.88dt-d).

If the second coefficient is nonnegative, replace S by C and use
`d+t>=1+.8dt` and `t^2<=.5`; the resulting bracket is at most -.017.
If it is negative, both terms are nonpositive. At S=t=0 the scalar
is zero, and the strict actual A point supplies the contradiction.
Therefore W.loU<d-2.88t, so exclusion of (1,2.88) must use upper V.

The lower face follows by excluding W.loU>=.76d-1.87t with the same
two support modes. Their scalar gaps become

    1-.24d-d(1-C)^2/2+t[.13-S(1-C/2)] > 0,
    Ct(.154d-.13t-1)+S(.74-.154t^2-.13dt-d) <= 0.

For the second expression, `d^2<=d` and the unit identity give
`d+.154t^2>=.154+.846d>=.7462`, so both coefficients have the required
sign. The far seed's other three bands then follow from W's marker,
forcing its lower V face. Finally its width obeys
`a<=1.01d+.24t`; the tangent inequality `.8d+.6t<=1` excludes t>=.51.

The new file is source-only. Both face proofs, their support identities,
strict band inferences, and the tilt deduction have received independent
mathematical review. No whole positive-central closure or global theorem
is claimed.

## Direct bottom-to-wall order in the missing-west-point branch

`Compact/Geometry/PositiveCentralEscapeOrder.lean` supplies the
conditional theorem `angle_order` for positive O and negative W.
It concludes `O.s<t` even when A misses (1,2). This closes the previously
missing entrance to an ordered O/L/W support cycle; it does not by itself
close that entire cycle or the original twelve-square case.

Write O=(p,q), W=(d,-t), A=(C,S). The true missing-west reduction gives
the O-axis separator and `q<S`. Let

    B(p,q)=1-2q+q(1-q)/p,
    U=2(C+S)-1, K=pC+qS, D=pS-qC, v=A.hiV.

Actual O containment, its next-marker exclusion, the strict side bound,
and A's center cap imply

    B(p,q) < D U + K(v-1).

Suppose `t<=q`. The parent's continuous algebraic comparison
`CornerOuterOrderMonotone.differences` shows that decreasing O's angle to
W's angle weakens this lower-face requirement. It uses a half-angle
substitution and two short sums of nonnegative products, not enumerated
angle values. Thus the same strict inequality holds at p=d,q=t.

The common bound at any q<=S is stronger than the vertical-axis value:

    C v > N + C(1-p),
    N=1+(C+S)(1-2S).

Its proof uses the exact difference

    (1-p)+q[(1-q)/p-(1-S)/C] >= 1-p,

and `K<=1`. The actual northwest-marker face cap then forces C>.81
and the endpoint comparison

    C(1.88C-S) <= N.

For A/W separation on A's V axis, the actual W left wall and foreign
top-seed cap imply

    v <= 1.88C-S+(1-d),

contradicting the strict common bound with p=d. The northwest cap is
essential in this endpoint step and is retained explicitly.

For A/W separation on W's U axis, put

    J=d^2-t^2, R=2J-(d+t)B(d,t).

After eliminating the true W faces, a necessary scalar is positive:

    R(C+S)+.88t(dC+tS)-J-dt-CS.

But `R<=d+t`, `C+S>=d+t`, and `dC+tS<=1` bound it above by

    R(d+t)+t-J-2dt <= 0.

The parent sourced that endpoint in `CornerOuterOrderEndpoint.lean`;
its exact factorization after multiplication by d is

    (1-d)[(1-d)-t(d^2+(1-d)^2)].

Both factors have the required signs since `1-d<=t/2` and
`d^2+(1-d)^2>=1/2`. This rules out `t<=q` in both genuine A/W modes.
The source has not been compiled. Its geometric wrapper has been sent
for independent source review. The wall exclusion at (1,2.88) remains
an additional premise, as the later original-packing audit establishes.

## Complete backward-U selectors for a negative left singleton

`CornerWallNegativeLarge.lean` now exports `left_axis_all` and
`wall_axis_all`. Together they close both outgoing support choices after
the backward L-U separator, for every canonical negative L=(l,-r).
Their premises retain actual O and L containment, O's upper-U cap,
the unconditional W upper-V cap, common side a>1, the angle order
s<=t<=.51 and d>=.86. The L-V theorem additionally retains the actual
L-owned corner and W-owned marker. No W upper-U cap or A(1,2) is used.

The incoming support bound is the exact full-square inequality

    c lower_O(l,-r) <= l(2c+s)-a[c(sl+cr)+l].

Combined with L's strict corner and its backward separator it yields

    (1-c)[cr-l(1-s)] > 0,

so the genuine angle restriction l(1-s)<cr follows, including exclusion
of the zero-bottom-angle endpoint. This restriction is used only where
required by the scalar proof; it was not imposed as a saved pose.

For r>=t, the wall's U coefficient E=rd-lt is nonnegative. Its actual
marker and top face therefore give

    lower_W(r,l) <= E(.914d-2t)+(rt+ld)(t+2.88d-a).

Using L's actual left wall and the incoming separator, the L-V choice
would force the common side below the scalar margin

    M = l+r-1 + X l^2
        + [c+d-2-.88d^2-.086dt]lr
        + [.086d^2+t(1-.88d)]r^2,
    X = s-1+(1-s)/c.

The parent's `CornerWallNegativeLeftMargin.margin` proves M>=0 using
the actual corner restriction. Its universal endpoint is reduced to
the cubic, with z=r/(1+l),

    .12-.828z+1.88z^2-z^3
      = (29/20)(z-207/725)^2 + 651/362500 + z^2(.43-z).

The remaining difference is three nonnegative products. For r<=t the
previous `CornerWallNegativeShared.sector` applies directly. Thus the
complete L-V selector now follows by a single order split.

For the W-V choice and r>=t, L's actual left wall gives the exact support
identity

    r upper_L(t,d)+d L.loU-a r(rt+ld)
      = (rt+ld)(l L.loU+r L.loV).

Its resulting scalar is

    F = 1-l+lX+r[c-2.88+(1-t)/d+l+rt/d] >= 0.

`CornerWallNegativeLargeBounds.wall_margin` proves this continuously.
At c=1,s=0, F0=(r/d)J where

    J=1-d[1.88-l-r/(1+l)]-t(1-r).

For r<=.4 an exact arc comparison bounds the response by the equal-angle
endpoint. For r>=.4 its two coefficients lie in a fixed disk strictly
inside the unit disk. If the bottom-angle correction F-F0 is negative,
the unit identities force r>=.49; the stronger disk estimate gives
J>=1/15. The possible loss is at most r/15 because

    (1-c)(c+s-1)/c <= 1/15

on c>=.86,s<=.51. This covers the correction without angle enumeration.

For r<=t the W-V support has an additional nonnegative side coefficient
p=tl-dr. Its exact normalized scalar identity is

    l F_small = M_shared + (rp/d)(l+r-d).

The parent's existing common-axis margin gives M_shared>=0, and the
remaining product is nonnegative because l+r>=1>=d. This completes the
second selector over all r.

All source remains uncompiled. The support identities and both new
scalar arguments have been independently reviewed by another agent.
The generic negative-W cycle assembly is owned by that agent; the
negative-O and positive-W entrances remain distinct tasks. No completed
global theorem is claimed by this checkpoint.

## Original-packing audit: the upper singleton premise is unavailable

The source-only original packing audit found a material entrance gap.
In the southwest chart the adjacent upper corner is code192, which is
a **paired corner**, not a singleton: C696 owner5 and C977 owner4.
`seedPoints (maskSupport 192)` supplies its two markers and corner (1,3).
It does not supply the singleton seed (1,2.88). Therefore W's exclusion
of (1,2.88) cannot currently be bound from these original owners.

This is not merely a missing theorem name. An axis square of side1.001
with x interval (0,1.001) and y interval (2.999,4) owns both paired
markers and (1,3), but misses (1,2.88). A disjoint axis W with the same
x interval and y interval (1.8795,2.8805) owns its marker (.914,2),
both required auxiliary points and (1,2.88). This two-square observation
does not refute the full packing; it identifies why the asserted seed
does not follow from the paired owner's local data.

The new sharp top face, t<.51, missing-Awest angle order, and completed
ordered cycle remain valid theorems with explicit hypotheses. Their
combination is **not yet a completed original C696/C977 signed cell**.
A genuine new geometric obligation or a replacement using the actual
upper-marker exclusion (.914,3) is necessary. All four C696 symmetry
charts have an adjacent paired corner, so transposition/half-turn alone
does not repair this premise.

The remaining entrance facts were checked directly against source:
C977 W8 universally owns auxiliary indices1,11; L1 owns0,10; A5 owns
4,13. C696 has the corresponding exact auxiliary assignment. Thus the
strict W points (1,2.26),(1,2.4), foreign L point(1,1.6), L far seed,
all marker negatives, common side bounds, containment and distinct-owner
disjointness are genuine. Canonical face reindexing preserves strict
interiors and side lengths and transports containment without moving a
physical square. No stronger finite pose assumptions are required.
