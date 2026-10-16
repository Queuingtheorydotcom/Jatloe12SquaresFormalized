# C1092: a uniform wall calculation and its physical entrance

Status: mathematical derivation and source-only Lean candidates, 11 October
2026. No Lean or Lake process, numerical producer, solver, angle search or
bulk archive extraction was run by this worker. The parent checked the small
rational identities and inequalities described below with exact Fractions.
That check is not Lean acceptance and does not prove the whole C1092 case.

## What is now smaller

`Compact/Geometry/C1092WallPolynomial.lean` contains one conditional theorem
`excludes_all_target_systems`. It covers all twelve original target points,
both boundary faces, all three point faces and every `t` in the closed
interval `[0,1]`. It includes the formerly missing 24 `P_face = 0` systems.
There are no angle subdivisions or interval certificates in the new proof.

The four arguments are two Euclidean projection bounds, one reusable
quartic square completion instantiated at five rational point coordinates,
and the corresponding cubic square completion. The cubic rule also handles
the endpoint of the quartic family. Lower target heights follow monotonically
from their six upper partners. The old 128/98/85 leaf inventories are not
dependencies of this calculation.

`Compact/Geometry/C1092WallPhysical.lean` additionally assembles the complete
physical point-forcing theorem `original_wall_point`. Its hypotheses are an
actual `OpenSquare`, `1<side≤1001/1000`, actual container containment, strict
ownership of marker12, absence of original markers0,1,8,11, and `centerY≤2`.
Its conclusion is strict membership of each of the twelve original targets.
Both sides of `centerX=1` are proved. The supporting modules are
`C1092WallCenterRegion.lean` and `C1092WallCenterCover.lean`. All four modules
are source-only and are not imported into the assembly.

The public `singleton_wall_point_cover` further removes the center-sign
premise: a square owning exactly marker12 has either the twelve lower
targets with `centerY≤2`, or their actual horizontal reflections with
`centerY≥2`. It transports foreign markers0/1/8/11 to6/7/11/8 and preserves
boundary equality. Other wall-owner directions still use the ordinary D4
packing transport; no claim that a packing itself is symmetric is made.

The source retains the eleven original residuals, including the exact
strictness of rows0–5. In particular `0<z2<1` is proved from rows4–5, not
silently assumed. It introduces no admissions, axioms or native checks.
It is not imported into the assembly and has not been replayed.

## Exact local system

Put `b=457/500`, `h=2-y`, `C=1-t²`, `S=2t`, `D=1+t²`.
Then `C²+S²=D²`, and on `[0,1]`, `C,S≥0` and `D>0`.
Write `r_i` for the original row residuals and `z=z2`.

For `P_face=0,B_face=0`,

```
r9+r10 = ((x-b)C+(y-1)S)z-D.
```

Every target satisfies `(x-b)²+(y-1)²≤1`; Cauchy gives the coefficient at
most `D`. Since `0<z<1`, this sum is strictly negative, contradicting its
nonnegativity. The distance bound also follows from the targets' simple
triangle constraints `x-b≥0`, `y-1≥0`, `(x-b)+(y-1)≤1`.

For `P_face=1`, independently of the boundary face,

```
C*r7+S*r8+D*r10 = D*((1-x)C+hS)z-D²/2.
```

Every target satisfies `(1-x)²+h²≤1/4`, so the same projection argument
excludes these 24 systems. There is no need for the previous degree-two
uniform certificate or its optimizer ancestry.

For `P_face=0,B_face=1`,

```
D*r6+S*r9+C*r10 = E*z-D(C+S),
E = bD²+(x-b)C²+(1-h)CS.
F(x,h,t) = D(C+S)-E
         = 1-x+2ht+(2x-4b)t²+(4-2h)t³-(1+x)t⁴.
```

If `F≥0`, the right side is negative because `D(C+S)>0` and `0<z<1`.

For a quartic `F=a0+a1*t+a2*t²+a3*t³+a4*t⁴`, select a rational `r` and put

```
f=F(r), g=F'(r), K=a2+2*a3*r+3*a4*r², G=a3+a4*(1+2*r).
```

The exact identity is

```
4K F(t) = (2K(t-r)+g)² + (4Kf-g²)
          +4K*t*(G+(-a4)*(1-t))*(t-r)².
```

Thus `a4≤0`, `K>0`, `G≥0`, `4Kf-g²≥0` prove the entire interval at once.
The five tuples and exact positive discriminants are:

| x | h | r | K | G | 4Kf−g² |
|---|---|---|---|---|---|
|457/500|1/1000|83/200|10028481/20000000|24769/50000|7830610336494519/4000000000000000000|
|23/25|3/500|41/100|30369/62500|617/1250|73279833071/156250000000000|
|47/50|27/1000|39/100|208329/500000|308/625|19322969679/156250000000000|
|24/25|1/20|9/25|4843/15625|661/1250|9841011/152587890625|
|49/50|19/250|13/40|14223/80000|581/1000|459307119/2560000000000|

At the sixth upper point, `x=1,h=53/500`,

```
F=t*(53/250-(207/125)t+(947/250)t²-2t³).
```

For a cubic with `a3≤0`, set `K=a2+a3*(1+2r)`. Its square-completion
identity is the same except that the last term is
`4K*(-a3)*(1-t)*(t-r)²`. At `r=7/25`, the endpoint cubic has
`K=167/250`, `f=109/78125`, `g=-16/3125`, and
`4Kf-g²=1446/390625>0`.

Increasing `h` increases `F` by `2*(Δh)*t*(1-t²)≥0`, so this covers both
heights at every x coordinate.

Finally, for `P_face=2`, independently of the boundary face,

```
S*r6+C*r8+D*r10 = W*z-R,
W=D*(xS+hC), R=(D²+S(C+S))/2>0.
R-D*(S+(197/500)C) = (1-t)*Q(t),
Q(t)=53/500-(447/500)t+(1053/500)t²-(447/500)t³.
```

The same cubic rule at `r=1/4` has `K=153/200`, `f=1/6400`,
`g=-69/8000`, and `4Kf-g²=25839/64000000>0`.
All targets have `x≤1,h≤197/500`, so `W≤R`; again `0<z<1` gives the
contradiction. This handles the closed endpoint `t=1`, where the displayed
margin vanishes, without losing the strict side-length premise.

## Exact map from an actual square to these rows

For a physical square of side `a>1`, center `(X,Y)`, and a face frame
`c,s≥0`, `c²+s²=1`, choose `t=s/(1+c)`; then `t∈[0,1]`, `c=C/D`,
`s=S/D`. This is face reindexing of the same square, not a symmetry
assumption on the packing. The existing `first_quadrant_rational` gives
this representation including axis endpoints.

Let `A=(b,2)` be strictly owned and set

```
z0=(c*(b-X)+s*(2-Y))/a,
z1=(-s*(b-X)+c*(2-Y))/a,
z2=1/a.
```

Owned A gives rows0–3 strictly, and `a>1` gives rows4–5 strictly.
The remaining common rows have the following physical meanings:

| Row | Exact residual after dividing by D | Required fact |
|---|---|---|
|6|`X/a-(c+s)/2`|left wall containment|
|7|`(1-X)/a`|`X≤1`|
|8|`(2-Y)/a`|`Y≤2`|

Let `B=(b,1)` be outside. Its relative coordinates divided by a are
`z0-s*z2,z1-c*z2`. Its two upper faces are impossible because A is strict
and `c,s,z2≥0`. The two lower faces give exactly the two row9 choices.

For `P=(x,y)` with `x≥b,y≤2`, the relative coordinates divided by a are

```
z0+(x-b)c*z2-hs*z2,
z1-(x-b)s*z2-hc*z2.
```

The upper-V face is impossible. The other three non-strict outside faces
give exactly the three row10 choices. Therefore, under actual left wall
containment, strict A ownership, outside B and `X≤1,Y≤2`, every one of the
twelve targets is strictly inside the physical square. Boundary ties remain
in the outside disjunction and are covered by the closed parameter interval.

## Why X≤1 cannot be assumed, and the actual complementary entrance

An exact single-square countermodel has

```
a=1001/1000, c=3/5, s=4/5, center=(6/5,2).
```

It fits inside `[0,4]²` (coordinate half-extent `7007/10000`), contains
marker12 strictly, excludes the other fifteen original markers, and has
`Y=2` but `X=6/5>1`. Its marker12 coordinates relative to its center are
`(-429/2500,286/1250)`, within half-side `1001/2000`. Marker8 has relative
V coordinate `-57/100`, and marker11 has U coordinate `11/20`, both outside.
This is a countermodel to a local localization implication, not a full
twelve-square packing or a counterexample to the desired theorem.

The original center-cover code explicitly handles X≥1 separately. Its
region is

```
R=conv{B,D,F,E} ∩ {X≥1,Y≤2},
B=(b,1), D=(33/20,33/20), F=(33/20,47/20), E=(b,3).
```

There is now a short source-only entrance in
`Compact/Geometry/C1092WallCenterRegion.lean`. The owned A and original
side cap imply `X<33/20` and `X<Y` by the circumradius bound. If
`Y<(325/368)X+1419/7360`, the center lies in the existing triangle0,
whose vertices are original markers0,1,8. Its diameter is below one, so
`triangle0_hit` forces one of these foreign markers strictly inside.
Hence every original marker12 owner in the X≥1,Y≤2 branch lies in R.
No saved polygon or auxiliary ownership alternative is needed for this
entrance. In original C1092, marker0/1 belong to owner0, marker8 to owner4,
and marker11 to owner7, all distinct from the marker12 owner8.

## A parametric replacement for the old center-cover polygons

Fix a target P=(x,y), put `d=33/20-x>0`, `h=2-y≥0`, `u=7/20`,
`H=h+u`, and `L=d²+H²`. All targets satisfy the short-edge inequalities
for the two triangles BDP and PDF, including `L≤1`. Also P lies above
BD and `b≤x≤1`. These two triangles cover the part of R below PF.
If the square avoided P as well as its actual foreign B,D,F, the triangle
nonavoidance theorem therefore forces its center above PF.

Write the remaining center as `(x+v,y+w)`. Its cap conditions are

```
v≥0, H*v≤d*w, w≤h.
```

The entire cap lies in the union of the closed radius-one-half disks around
P and F provided

```
(d²+u²-h²)²+4*d²*h² ≤ d².                 (Disk)
```

Here is a direct proof without any polygon or Voronoi enumeration.
If `w≤H/2`, then `v≤d*w/H` gives
`v²+w²≤L/4≤1/4`. Otherwise `w≥H/2`. Put
`J(w)=L*((2w-H)²+d²)`; it increases on `[H/2,h]`, and (Disk) says
`J(h)≤d²`. For the closer of P and F, the bisector inequality gives

```
4*d²*min(v²+w²,(d-v)²+(H-w)²) ≤ J(w) ≤ J(h) ≤ d².
```

For P this follows by squaring `0≤2dv≤L-2Hw`; for F use
`0≤2d(d-v)≤d²-H²+2Hw`. These are exactly the two sides of the
perpendicular bisector. Thus one disk contains the center. Since `a>1`,
every point at distance at most1/2 from the center is strictly inside the
square. This contradicts avoidance of both P and F.

The parent checked (Disk), BD, BP, DP and PF squared-length bounds exactly
for all twelve targets. The smallest displayed disk slack is still positive:
target6 has `29132559/10^12`. This is a twelve-point arithmetic check of one
parametric planar theorem, not a generated center cover or an angle search.
The disk lemma, explicit barycentric coordinates for both triangles, target
arithmetic and actual-square adapters are now assembled as source in
`C1092WallCenterCover.lean` and `C1092WallPhysical.lean`. They have not been
accepted by Lean. The physical left branch reuses the uniform inequalities
directly in centered face coordinates, rather than assuming that a physical
square already supplies a polynomial system.

## Remaining global boundary

This work supplies the complete symbolic local wall calculation and its
physical point-forcing entrance for an original C1092 wall owner under the
selected center sign, with a source-only Lean assembly. The former local
wall-calculation gaps in center localization and face decomposition are
resolved by the arguments above. It does not exclude a
twelve-square packing. Whole C1092 still requires the four wall-sign orbit
cover, all other retained auxiliary assignments and their parent deductions,
the residual ownership cover, the maximal-angle normalization and full
35-bin ancestry/closure, or a new mathematical argument replacing those
parts. In particular, the central pinwheel frame/center bounds are separate
from the wall-owner center region proved here. None of those global
obligations is inferred from the 72 local systems.

Primary source members read, without executing their producer code:

* `12-square-formalization-partial-work.zip/current/C1092/...` (the four
  recovered Lean drafts and original row verifier; actual archive includes
  the outer `12-square-formalization-partial-work/` directory).
* Historical `entrance-replay/research/wall_forced_region.py` and
  `side_center_segment.py`, which expose the separate X≥1 center cover.
* Historical `CASE1092-DRAFT.md`, the original marker grouping and coverage
  obligations, plus the named pinwheel boundary/axis/corner source files.
* Current `S12/Markers.lean`, `SquareFrame.lean`, `WallGeometry.lean`,
  `CenterLocalization.lean`, `MarkerCoverGeometryBase.lean`, and
  `TriangleCover.lean` for the unchanged geometric semantics.
