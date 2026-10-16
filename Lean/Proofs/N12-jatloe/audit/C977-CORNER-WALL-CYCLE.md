# C977: a continuous corner–wall support cycle

This is a mathematical source checkpoint, not a checked Lean result or a
whole-family exclusion. The preferred `CornerWallMarkerCycle.impossible`
now covers every signed canonical L and every surviving support selector
using genuine marker faces, with the outer angle order explicit.
`C977OwnedWestCorner.frame_excludes` binds the complete owned-west-point
positive-bottom/negative-wall sector to the original C977 packing.
All sources are uncompiled. No numerical enclosure is used.

**Historical interface gap:** the older `CornerWallOrderedCycle` sharp wall face
`W.hiV≤t+2.88d` uses W missing `(1,2.88)`. In both C696 and C977 the
adjacent NW owner has paired mask192, whose original seeds supply the two
markers and `(1,3)`, not `(1,2.88)`. Existing exact local square models
show that the pair need not contain this latter point. Consequently the
sharp face, `t<.51`, and `d>.86` are conditional here; the assembled cycle
does not yet exclude an original packing. The genuine marker face
`W.hiV≤.914t+3d` is the next interface to investigate, together with the
full NW square. The C977 family remains 50 ownership vectors.

## Genuine-marker replacement checkpoint

Both signs of L have now been rebuilt with genuine marker faces and
assembled as `CornerWallMarkerCycle.impossible`. Its explicit outer order
is `s≤t`; its wall range is the genuine `t≤3/5`, `d≥4/5`. It uses

```
O.hiU≤2c+.914s,
O.hiV>1+s/c−2s−.914s²/c,
W.hiV≤.914t+3d,
W.hiU≤1.65d−2.35t.
```

`NegativeWallMarkerCap` derives both W caps from its actual marker,
foreign NW and upper-corner markers, and the valid lower face
`W.loV≥.76t+1.87d`. The width gives `t<825/1387<.6` and `d>.8`.
The extra point `(1,2.88)` is absent from this replacement.

Every positive-L selector has a continuous source proof:

| O/L separator | L/W separator | Genuine-marker source |
| --- | --- | --- |
| O-v | W-v | `CornerWallCycle` (already used the weaker top cap `t+3d`) |
| L-v | L-v | `CornerWallMarkerShared` |
| O-v | L-v | `CornerWallMarkerMixed` (both relative angle orders) |
| L-v | W-v | `CornerWallMarkerOtherMixed` |
| O-v or L-v | L-u | `CornerWallMarkerLongitudinal` and its scalar bounds |

The shared selector retains the exact support width
`extra=max(0,sl−cr)`. For its coefficient vector A,B,

```
A=c+t−3+(1−.914t)/d,
B=s+d−2+(1−.914s)/c,
A+s²≥−(c+d)/2,
B−cs≥−(s+t)/2.
```

Because `extra≥s(sl−cr)`, the scalar is bounded by the average of two
unit-normal dot-product margins. This is the width discarded in the
earlier argument.

The O-v/L-v selector has one scalar norm for both relative angles. Put
`B0=1+s/c−2s−.914s²/c`, `G=(B0+s)/c`, and
`P=G+t+(1−t)/d−3`. The exact source proves

```
P²+(1−d)²≤1,
```

using monotonic G and a cubic endpoint identity in `1−d`. When L tilts
farther than O, the actual marker gives `L.loU<.914l+r`. The remaining
support correction is

```
((cr−sl)/(c(cl+sr))) * [.086cl−r(c−s−B0)] ≥ 0.
```

Its sign follows from `(1−c)(1−s)≤1/12<.086`. Thus the older artificial
wall-point cap and its adjusted norm are unnecessary for this half.

Every negative-L selector now also has a continuous source proof:

| O/L separator | L/W separator | Genuine-marker source |
| --- | --- | --- |
| O-v | W-v | `CornerWallCycle` |
| O-v | L-v | `CornerWallMarkerNegativeMixed` |
| L-u backward | L-v or W-v | `CornerWallMarkerNegativeLarge` |

In the backward branch the actual strict L corner and true bottom marker
cap force `c<.914` and `r>.6`. This removes the older small-negative-L
branch entirely. The two remaining scalar margins use the genuine top
marker, with no fabricated point or small pose interval.

The high-angle negative mixed branch uses both genuine W caps. Put

```
X=3-.65t²-.736dt+t-d,
Y=1.65-.736t²+.65dt-d-t.
```

Its response increases continuously from the wall angle to the L angle.
For two unit normals set `Q=l+d`, `R=r+t`, `x=Q-R`. The exact
finite-difference coefficient is bounded by

```
H=(Q²-R²)/2-.75QR+1.75R-.65Q
 = (7/40)x²+(1/50)(2-x)+(3/8)(4-Q²-R²)
   +(x+11/10)(R-7/5+(7/10)x) ≥ 0.
```

The terms are nonnegative because the normals are canonical,
`Q²+R²≤4`, and `7Q+3R≥14`. At the wall angle the response is the
already proved disk margin plus `.086t`. This supplies the complete
arc without angle samples, derivatives, or extra singleton seeds.

The original C977 adapter chooses the left frame internally and derives
its strict corner from `C977CornerReach`. The actual wall owner8 supplies
marker `(.914,2)` and auxiliary `(1,2.4)`; its exclusions of the original
NW and upper-corner markers, together with the actual left singleton's
far seed `(.76,1.87)`, supply the two W faces. The existing owned-west
order theorem then supplies `s<t`. Thus this entire signed-L sector now
has its actual-packing entrance, not merely free marker hypotheses.
Root and midpoint independently read the original owner/point adapter;
both reported no strengthened premise or mapping error.

**Remaining boundaries:** all of these replacements are uncompiled.
The genuine outer angle order is currently available when the central
square owns `(1,2)`; the missing-point order source still depends on the
unavailable 2.88 premise. `CornerWallMarkerCycle.Data.order` deliberately
retains that gap. A verified three-square O/A/W countermodel also shows
that the missing-point order cannot follow from those three squares
alone; the actual L/A interaction is still required. The new owned-west
adapter excludes one orientation/incidence sector, not all C977
orientations or any complete ownership vector. The 50-vector boundary
is unchanged.

## A complete selected-sector contradiction

Let the actual bottom singleton `O`, left singleton `L`, and left wall
square `W` have common side `a>1`. Write their canonical unit normals as

- `O=(c,s)`, where `0<s≤c`;
- `W=(d,-t)`, where `0≤t≤d` and `s≤t`;
- either `L=(l,r)` or `L=(l,-r)`, with `0≤r≤l`.

The first two calculations below handle `r≤s` in the positive frame and
`r≤t` in the negative frame. The subsequent support-corner correction
extends them to every canonical orientation of L.

The selected actual separating axes are

```
O.hiV ≤ lower L (-s,c),
upper L (t,d) ≤ W.loV.
```

The first says O lies below L on O's transverse axis, and the second
says L lies below W on W's transverse axis. Boundary contact is allowed.
Retain the actual left containment of L. The original marker exclusions
and bottom containment of O give

```
O.hiV > 1+s/c-2s-(457/500)s²/c.
```

The original upper-marker exclusion of W gives
`W.hiV≤(457/500)t+3d`. Both follow from the full square geometry in
`C696PositiveCorner.corner_faces` and `LeftWallNegativeFaces.faces`.

Relax both marker coefficients to 1, and put

```
B=1+s/c-2s-s²/c.
```

Then `O.hiV>B` and `W.hiV≤t+3d`. This weakening makes the scalar part
independent of all decimal constants and of the stronger bound `t<3/5`.

### Extracting the full-width chain

For positive L set `D=cr-sl≤0`, `K=cl+sr`. Actual O/L separation is

```
O.hiV≤D L.hiU+K L.loV.
```

The actual left wall says `l L.loU≥r L.hiV`. Consequently

```
L.loV≥(l/c)O.hiV-a(D/c)(l+r).
```

The coefficients of `(t,d)` in L's frame are `tl+dr` and `dl-tr`,
both nonnegative. Using the same actual left wall a second time gives

```
upper L (t,d) ≥ (d/c)O.hiV
                  +a[l(t+d)+(ds/c)(l+r)].                 (1)
```

The two separated square widths and the W cap therefore require

```
(d/c)B+1+l(t+d)+(ds/c)(l+r)-t-3d < 0.                     (2)
```

The strict inequality is supplied by `a>1` and `O.hiV>B`, so the scalar
part need only be nonnegative, including all endpoint orientations.

### Two exact endpoint inequalities

The expression involving `(l,r)` in (2) is a positive linear functional
on the unit arc from `(1,0)` to `(c,s)`. Its minimum is at an endpoint.
One entirely algebraic proof uses

```
l ≥ 1-r(1-c)/s,
```

which follows from `(1-l)/r=r/(1+l)≤s/(1+c)=(1-c)/s` when `r>0`;
`r=0` is the endpoint. Thus no calculus or discretization is needed.

At `L=(1,0)` let

```
F0=(d/c)B+1+t+d+ds/c-t-3d.
```

The exact identity

```
c² F0=c²-d[c²+(1-c)(1-s)]
```

and `d≤c` imply

```
c² F0≥c(1-c)(c+s-1)≥0.                                 (3)
```

At `L=(c,s)` put

```
Q=2/c+s-3-2s/c+s(1-s)/c²,
F1=1+dQ+(c-1)t.
```

The identity

```
c²(Q+c)=-(1-c)[c²+(1-c)(1-s)]
```

gives `Q≤-c`. Unit-normal Cauchy gives
`c(c-d)≥s(t-s)`, because their difference is `1-cd-st≥0`.
Since `c+s≥1`,

```
F1(d,t)-F1(c,s)
  =Q(d-c)-(1-c)(t-s)
 ≥c(c-d)-(1-c)(t-s)
 ≥(c+s-1)(t-s)≥0.
```

Finally the equal-angle endpoint factors exactly:

```
c F1(c,s)=(1-s)(1-c)(2c-1)≥0.                           (4)
```

Canonical normals ensure `c≥1/√2>1/2`. Equations (3) and (4) contradict
(2), proving the complete positive-L sector `r≤s`.

### The negative-L sector uses the same endpoints

For `L=(l,-r)`, with `0≤r≤t`, actual left containment is
`l L.loU+r L.loV≥0`. The same selected support axes instead give

```
upper L (t,d) ≥ (d/c)O.hiV
                  +a[l(t+d+ds/c)+tr].                   (5)
```

Its positive linear functional again has its minimum at the two unit-arc
endpoints `(1,0)` and `(d,t)`. The first is exactly F0. At `(d,t)` the
width coefficient is `1+dt+d²s/c`. It dominates the positive-L endpoint
coefficient `ct+ds+d/c` because

```
1+dt+d²s/c-(ct+ds+d/c)
  =((c-d)/c)(1-ct-ds)≥0.
```

Here `c≥d`, and `ct+ds≤1` is another unit-normal Cauchy inequality.
Thus (3) and (4) also contradict the complete negative-L sector `r≤t`.

### The changing support corners close the remaining L angles

For positive L with `r≥s`, put `D=cr-sl≥0`. The lower support of L on
O's transverse axis uses `D L.loU` rather than `D L.hiU`. The exact
support chain therefore gains the full-width term `adD/c`. Its new
coefficient is

```
P=l(t+d)+dr(1+s/c).
```

It dominates the equal-O-angle coefficient `ct+ds+d/c`. To see this,
put `u=c-l≥0`, `v=r-s≥0`. Unit-normal identities give
`u(c+l)=v(r+s)`, while

```
(c+s)(c+l)-2c(r+s)
  =(c+s)(l-r)+(c-s)(c-r)≥0.
```

Both frames are canonical, so `r≤c`. Consequently
`2cu≤(c+s)v`, and

```
c[P-(ct+ds+d/c)]
  =d[(c+s)v-2cu]+c(d-t)u≥0.
```

Thus (4) covers this entire range too.

For negative L with `r≥t`, the coefficient `p=tl-dr` in W's transverse
support is nonpositive. The upper support of L uses `p L.loU` rather
than `p L.hiU`, adding the full-width term `-ap` to (5). Its new
coefficient is

```
P=dl(1+s/c)+r(t+d).
```

Canonical unit normals give `d-l≤r-t`. Also
`t+d≥d(1+s/c)`, since `t≥s` and `d≤c`. Therefore this P dominates
its value at `(l,r)=(d,t)`, already handled by (3) and (4).

These four sign/order ranges exhaust every signed canonical L. There
is no remaining L-angle restriction in the selected pair of axes.

### A short exact support identity

The full-width extraction does not require intermediate position bounds.
Write `H=O.hiV` and `h=ct+ds`. In the initial positive range, let

```
wall=l L.loU-r L.hiV,
sep=(cr-sl)L.hiU+(cl+sr)L.loV-H,
C=cl(t+d)+ds(l+r).
```

Then the exact identity is

```
c upperL(t,d)-dH-aC=h wall+d sep.
```

Both terms on the right are nonnegative by actual containment and
actual separation. In the other three sign/order ranges, use the
appropriate actual support corner and the corrected coefficient above;
the same identity holds. `CornerWallCycle.transverse_sector` records
this direct square-support proof.

## Precise remaining coverage

This calculation uses the full side of L, its actual left container
wall, and both actual support separators. It does not replace L by its
seed segment. It excludes two entire continuous orientation sectors,
not two ownership vectors.

The additional missing point `(1,72/25)` would strengthen the W face to
`W.hiV≤t+(72/25)d`. `LeftWallTopSeed.upper_face` proves this from the
earlier U cap; the separate `NegativeWallTopSeed` source derives it without
the disputed central point by using actual A/W separation. This missing
point is not currently available from the C696/C977 paired NW owner.

For positive L, the remaining transverse selectors now have the following
source coverage, all uncompiled:

| O/L axis | L/W axis | Coverage |
| --- | --- | --- |
| O-v | W-v | Every canonical L; `CornerWallCycle` |
| L-v | L-v | Every canonical L; `CornerWallSharedAxis` |
| O-v | L-v | `r≤s`: `CornerWallMixedAxis`; `s≤r`: `CornerWallLastPositive` |
| L-v | W-v | Every canonical L; `CornerWallOtherMixed` |

The shared-axis scalar is proved in the root-owned
`CornerWallSharedMargin.lean`. For

```
A=c+t-72/25+(1-t)/d,
B=s+d-2+(1-s)/c,
```

it establishes `A²+B²≤249901/250000<1` when `s≤t≤3/5` and `d≥4/5`.
Thus `1+lA+rB>0` for every unit L. Actual bottom containment of O and
left containment of W extract exactly this coefficient vector.

The first mixed selector, when `r≤s`, dominates this shared margin by

```
((sl-cr)/c)[l+r+s-2+(1-s)/c]≥0.
```

For the second mixed selector, the range `r≤t` follows from the shared
margin multiplied by `d/l`, plus `(tl+dr)(l-d)/l≥0`. When `r≥t`, its
remainder is bounded below by

```
l+d(1+l²-3l)+t(l²-l)≥0.
```

The exact certificate is

```
l²-(1+l²-3l)²-(l²-l)²=(1-l)²[1-2(1-l)²]≥0,
```

followed by unit-normal Cauchy. The coefficient relaxation uses only
`c≥4/5` and `c+s≤10/7`.

The last positive-L range O-v / L-v with `r>s` is now sourced in
`CornerWallLastPositive`. It additionally uses the actual owned L corner
`(1,1)` and the conditional stronger wall range `t≤51/100`, `d≥43/50`.
Its adjusted coefficient vector has squared norm at most
`993037/1000000<1`; see `C977-LAST-POSITIVE-L-SECTOR.md` for the exact
continuous derivation. All four positive-L transverse selectors therefore
have source under their stated premises, still without compilation.

For negative L, the current source coverage is:

| O/L axis | L/W axis | Coverage |
| --- | --- | --- |
| O-v | W-v | Every canonical L; `CornerWallCycle` |
| O-v | L-v | Every canonical L; `CornerWallNegativeMixed` |
| L-u backward | L-v | Every canonical L; `CornerWallNegativeLarge.left_axis_all` |
| L-u backward | W-v | Every canonical L; `CornerWallNegativeLarge.wall_axis_all` |

Both backward ranges now have source proofs. The negative
O-v / L-v proof uses the actual W marker when `r≥t`, so it does not assume
the disputed W upper-U cap. Its scalar comparison has a margin of at
least `1/50` at the horizontal endpoint for `r≤t`; for `r≥t` it reduces to

```
(1-l)(1-(3/5)l)+r(l-457/500)≥0.
```

When `l≤457/500`, canonical `r≤5/7` gives the exact certificate

```
(1-l)(1-(3/5)l)-(5/7)(457/500-l)
  =(3/5)(l-3/4)^2+l/70+27/2800>0.
```

The positive-L longitudinal L/W selector is now excluded without a
lower L-tilt restriction by `CornerWallPositiveLongitudinal` and
`CornerWallPositiveLongitudinalBounds`. This retains actual O/L coupling
and W's marker; it uses the conditional sharp face and tilt range above.

The preceding `PositiveCentralWallAngleOrder` source proves `t>s` with
the central point `(1,2)` explicit. The separate new
`PositiveCentralEscapeOrder` source derives the same outer angle order
when that point is missing, using the original northwest-marker face and
actual A/W separation. Its scalar and support algebra have been
independently read, but it too remains uncompiled. Its sharp top-point
premise has the same original-packing entrance gap. All generic selectors
are assembled; genuine original face/order premises must still be supplied
before this becomes an original four-square exclusion.
The 50-vector C977 ending is not proved by this checkpoint.
