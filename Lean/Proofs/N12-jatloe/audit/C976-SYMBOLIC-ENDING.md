# C976: joint geometry of the eleven residuals

Status: mathematical source audit, 2026-10-11. No compiler, interval search,
solver, trace producer, or numerical experiment was run for this note. The
new deductions below have not been translated into Lean. They do not prove
any whole residual exclusion.

## Original entrance and the small parameter family

The original entrance is `S12.case976_aux_reduction_to11`, used by
`Completion/Cases/C976/Reduction.lean` and `Residuals.lean`. It retains the
actual normalized packing, common side `1 < a <= 1001/1000`, containment,
pairwise disjoint interiors, exact marker ownership, and exact combined F/G
ownership. The eleven rows must not be assumed without this entrance.

Owners 0 through 11 have marker masks
`[1,2,12,48,192,256,512,1024,6144,8192,16384,32768]`.
Only owners 6 and 7 change their auxiliary signature:

| Original Lean vector | Owner 6 | Owner 7 |
|---|---|---|
|25|F8,G8|F5,G7|
|28|F8,G8|F5,G6,G7|
|30|F8,G8|F7,G6|
|36|F8,G8|F7,G7|
|42|F8,G8|F7,G6,G7|
|45|F8,G8|F5,F7,G6|
|47|F8,G8|F5,F7,G7|
|49|F8,G8|F5,F7,G6,G7|
|50|F8,G6,G8|F5,G7|
|52|F8,G6,G8|F7,G7|
|55|F8,G6,G8|F5,F7,G7|

Here F5=(2,2.26), F7=(2.4,3), F8=(3,1.74), G6=(2.26,2),
G7=(2.26,3), and G8=(3,1.6). All decimals in this note denote exact rationals.
An absent F/G point is excluded by that owner's exact signature. An absent
point need not belong to another owner.

The useful fixed central/wall data are:

| Owner | Strict owned points relevant here |
|---|---|
|5|(1.65,1.65), (2,1.74), (1.74,2)|
|6|(2.35,1.65), (3,1.74), (3,1.6)|
|7|(2.35,2.35), and its varying auxiliary points|
|8|(.914,2), (1.65,2.35), (1,2.26), (1,2.4)|
|9|(2,.914), (2.26,1), (2.4,1)|
|10|(3.086,2), (3,2.26), (3,2.4)|
|11|(2,3.086), (1.6,3), (1.74,3)|

`InitialHull.owners_query_inside/outside` is the original interface that
proves these facts. In particular, owner 8 really owns both the left wall
marker and the northwest central marker. Treating the latter as missing is
an invalid application of the ordinary four-square template.

## Shared consequences without angle subdivisions

The checked `WallLowerBarrier.left_positive_point`, after an internal frame
change and the appropriate D4 transformation, gives all eleven vectors:

```
owner 9  owns (2.5,1)
owner 10 owns (3,2.5)
owner 11 owns (1.5,3)
owner 8  owns (1,2.5).
```

For owner 9 use `(x',y')=(y,x)`; for owner 10 use `(4-x,y)`; for owner 11
use `(4-y,4-x)`; for owner 8 use the identity. Each transformed square owns
P=(.914,2), Q=(1,2.4), and excludes W=(1,1.74), D=(1.74,2).
These are literal signature consequences, not extra geometric assumptions.
The parent's strengthened wall argument is intended to replace 2.5 by
2.56, and the transformed 1.5 by 1.44; that stronger theorem needs its own
replay before an assembled proof may use it.

The fixed occupied row y=1.74 has points x=1,2,3 belonging to owners1,5,6.
The fixed occupied column x=1.74 has points y=1,2,3 belonging to owners0,5,11.
The existing radius/occupied-row theorem consequently gives several common
center cuts. They do not by themselves contradict the packing.

Vectors 28,42,49 give owner7 a strict vertical unit segment from (2.26,2)
to (2.26,3). The strict unit-span lemma being developed by the C981 worker
therefore gives a horizontal section longer than 1 at y=2.5. Since owners8
and10 occupy the slots x=1,3, owner7 must contain (2,2.5). There is no known
third foreign occupied slot at x=2. This is a forced point, not a completed
contradiction.

## A stronger shared contraction using a finer occupied row

Set delta=457/500=.914 and, in a canonical frame, write

```
c>0, 0<=s<=c, c^2+s^2=1,
rho_delta = (c+s-2*delta*c*s)/2.
```

For either sign of the frame's second coordinate, a square of side a>1
has a horizontal section longer than delta at height h whenever
`|centerY-h| <= rho_delta`. This is the usual chord formula, with chord
length delta rather than 1. One elementary proof uses the centered closed
unit square: its section length is

```
min(1/c, ((c+s)/2-|h-centerY|)/(c*s))
```

when s>0. Both expressions are at least delta under the stated condition.
The original side a>1 supplies strict room; s=0 is the axis case. This
needs an actual generalized chord lemma, not a rescaling of the old radius
formula with the wrong side parameter.

The four positions `.914,1.74,2.26,3.086`, together with endpoints0,4, have
all consecutive gaps at most delta. Thus any open interval of length
greater than delta in [0,4] contains one of those four positions.

For vectors28,30,42,45,49, G6 belongs to owner7. All four positions on y=2
are therefore occupied by owners8,5,7,10, distinct from owner6. Owner6
cannot have the indicated long section. Its own two points

```
P=(2.35,1.65), Q=(3,1.6)
```

also rule out the upper alternative `centerY >= 2+rho_delta`, uniformly
over orientations. If its canonical frame is (c,s), the upper face bounds
from P.U and Q.V give

```
centerY < 1.6 + .05*s^2 - .65*c*s + a*(c+s)/2.
```

If its frame is (c,-s), the lower U bound from Q and upper V bound from P
give instead

```
centerY < 1.65 - .05*s^2 - .65*c*s + a*(c+s)/2.
```

After subtracting `2+rho_delta`, the first bound is at most
`-.4+.025+.132+.00075<0`, and the second at most
`-.35+.132+.00075<0`. Here `s^2<=1/2`, `cs<=1/2`, `c+s<=3/2`,
and `a-1<=1/1000` suffice. Consequently all five vectors satisfy

```
centerY(owner6) < 2-rho_delta(owner6).
```

For vectors50,52,55, G6 instead belongs to owner6. The same occupied mesh
is entirely foreign to owner7; its strict point at height3 chooses the
upper alternative, so

```
centerY(owner7) > 2+rho_delta(owner7).
```

The last assertion follows directly from the usual upper-anchor argument:
`centerY > 3-a(c+s)/2 > 2-rho_delta`, since
`1-(a-1)(c+s)/2-delta*cs > 0`.
The three remaining vectors25,36,47 do not assign G6 to either owner.
The four-point row must not be inserted in those vectors.

## A small angle reduction for vector42

The following is an exact local lemma, requiring no containment or side
upper bound. Let B have side>1, canonical frame (c,s) with c>0 and |s|<=c,
and strictly contain P=(2.26,2), Q=(2.26,3). Suppose B excludes
Z=(2,2.26), and is disjoint from a square R whose closed hull contains
the vertical segment `(3,2.26)--(3,2.56)`. Then

```
s > (28/37)*c.
```

Proof. Z's V projection lies between those of P and Q, for every canonical
frame. Its U projection is below at least one of the two owned projections,
so Z can only fail below the lower U face. Thus `U(Z)<=loU(B)`.

If s<=0, R's point (3,2.26) has V projection between P.V and Q.V.
Its U projection is above the lower owned projection and exceeds U(Z)
by exactly c<=1<side. It is therefore strictly inside B, a contradiction.
The same argument works for `0<=s/c<=13/37`.

For `13/37<=s/c<=28/37`, put

```
e=(37/50)*(s/c)-13/50,
H=(3,113/50+e).
```

Then 0<=e<=3/10 and H is in the foreign closed segment. Directly,
`V(H)=V(P)` and `U(H)-U(P)=.74/c>0`. Also

```
U(H)-U(Z) = c+e*s = (1-.26*s*(s+c))/c <= 1.
```

For the last inequality, `s/c<=28/37<4/5` implies c>=3/4. Hence
`1-c=s^2/(1+c)<=4*s^2/7<=.26*s*(s+c)`;
the final comparison follows from s/c<=4/5 since
`(4/7-13/50)*(4/5)=218/875 < 13/50`.
Again H is strictly inside B, contrary to disjointness.

Vector42 supplies exactly these premises with B=owner7 and R=owner10
once the parent's 2.56 wall point is proved. Without that strengthening,
the already proved 2.5 point gives the analogous, weaker cutoff
`s>(25/37)c`, by the same argument.

## Why this does not yet close the steep sector

An exact local square remains feasible:

```
c=21/29, s=20/29, side=1001/1000,
loU=8733/2900, loV=-1/5.
```

It has exactly marker10 and auxiliary signature `{F7,G6,G7}`. For example,
the U projections of F5 and G6 are respectively `4360/1450` and
`4373/1450`, so loU lies strictly between them. G7 has U=`5373/1450`;
its V is `89/145`, inside `(-.2,.801)`. F7 has U=`5520/1450` and
V=`15/29`, also inside. Marker10 has U=`1927/580` and V=`47/580`.
The four extremal x/y coordinates lie respectively in (1.62,1.64),
(3.04,3.05), (1.93,1.94), and (3.34,3.35), hence the square is contained.

All the displayed neighboring compulsory hulls are excluded by a single
face for each owner. In particular, owner10's strengthened segment is
below V=-.2: its upper endpoint has V=`-156/725`. Owner11's point
(2,3.086) is above the upper V face, with V=`12403/14500>.801`;
its other displayed points are still higher in V. The owner8 hull is
entirely below the lower U face. The other central hulls are separated
by lower U or lower V.

This is not a twelve-square packing: no positions/orientations have been
assigned to the neighboring squares. It shows precisely why compulsory
point hulls and the new angle cut do not finish vector42. A valid next
step must use the actual neighboring squares' support and wall constraints,
including their interaction with corner owners, rather than treating
another unproved point or small-angle localization as given.

## Remaining coupled obligation

The old `PositivePinwheel.lean` proves a useful continuous terminal theorem
only after four central half-angles are in `[0,1/64]`, four boundary
half-angles in `[-1/32,1/32]`, and its concrete localization structure is
established. Its own source explicitly leaves these entrances open.
The cuts above do not establish them: vector42's local witness has
half-angle `s/(1+c)=2/5`.

A compact C976 completion therefore still needs one of:

1. A joint wall/core argument excluding the large-angle alternatives and
   proving the small-angle/sign/localization entrance to the existing
   pinwheel terminal theorem; or
2. A full-angle replacement for that coupled terminal theorem, with the
   original square support constraints and exact eleven-vector entrance.

The new mesh cuts share one algebraic proof across eight vectors, and the
angle cut reduces one residual without enumeration. Neither gives a
certificate-size bound for the remaining coupled argument. No completed
residual count or eventual million-line guarantee follows from this note.
