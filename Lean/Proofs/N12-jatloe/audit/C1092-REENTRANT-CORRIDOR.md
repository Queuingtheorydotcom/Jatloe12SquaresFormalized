# A physical-square obstruction beyond the C1092 point relaxation

Status: handwritten mathematical proof and Lean source, 11 October 2026.
No compiler, solver, search or producer was run for these modules. The
source has not been elaborated. This is not a whole C1092 exclusion.

## Uniform corridor capacity

Let an open square of side `a>0` lie in the first quadrant. Then its closure
contains a point with both coordinates at least `a`. This holds at every
orientation, including axis directions.

Choose the square's face coordinates with `c,s≥0` and `c²+s²=1`. Write
`X,Y` for its center and `z=c+s>0`. Containment in the quadrant gives

```
u = X-a*z/2 ≥ 0,       v = Y-a*z/2 ≥ 0.
```

Since `c,s≤1`, the identity `(1-c)(1-s)≥0` gives `1+cs≥c+s`.
Consequently

```
r = a*(1+cs)/(c+s) ≥ a.
```

The point `P=(u+r,v+r)` is in the closed square. Indeed, if `loU,loV`
are its lower face coordinates, direct calculation gives

```
c*Px+s*Py = loU+a,
-s*Px+c*Py = loV+a*c/(c+s),
```

and `0≤c/(c+s)≤1`. Thus `Px,Py≥a`. For any `0≤d<a`, a sufficiently
small move from P toward the center is strictly inside the square and
still has both coordinates greater than d. The source uses the explicit
fraction `t=(a-d)/(2a)` for that move.

It follows that a square of side a cannot lie in

```
{x≥0, y≥0, x≤d or y≤d}
```

when `d<a`. More generally, unequal corridor widths `d₁,d₂<a` are
excluded by taking `d=max(d₁,d₂)` (provided they are nonnegative).
No selected separating axis, angle cell or finite target list enters the
argument.

`Compact/Geometry/ReentrantCorridor.lean` proves the closed northeast
point, an interior point beyond two narrower strips, and `side_le_arm`.

## Application to the parametric eight-square windmill

Keep the original container `[0,4]²`, and let `1<a≤1001/1000`. Consider
the eight axis-parallel squares from the exact point-relaxation model,
now with variable a:

```
(0,0), (4-a,0), (4-a,4-a), (0,4-a),
(a,4-3a), (2a,a), (4-2a,2a), (4-3a,4-2a).
```

All listed pairs are lower-left corners, and every square has side a.
Suppose a ninth square q of side a is contained in the box, strictly owns
the original left wall marker `(457/500,2)`, and has interior disjoint
from the four neighboring squares with lower-left corners

```
K=(0,0), C=(a,4-3a), T=(4-3a,4-2a), H=(0,4-a).
```

There is no assumption on q's orientation or center sign. The source
proves these premises impossible:

1. The closures of K,C,T,H cover the complete line segment
   `x=a, 0≤y≤4`. A point strictly inside q cannot belong to any of these
   closures: an open neighborhood in q would intersect the foreign open
   square. Since the marker has x<a, convexity gives `q⊂{x<a}`.
2. On this side of the cut, K covers `y=a` and H covers `y=4-a`.
   The marker lies between them, so the same convexity argument gives
   `a<y<4-a` throughout q.
3. Every point of q with `x>4-3a` and `y>4-2a` would lie in the closure
   of T, using the preceding upper bounds. Therefore every point of q
   satisfies `x≤4-3a` or `y≤4-2a`.
4. Translate q down by a. It is now a square in the first quadrant,
   contained in the corridor with equal arms `d=4-3a`. Here `d≥0` and
   `d<a`. The corridor capacity theorem is a contradiction.

Thus the exact eight-square countermodel cannot be completed even by its
left wall owner, uniformly over the entire real side interval and every
orientation and translation of that missing owner. The other missing wall
directions follow by rigid rotation, but are unnecessary for exclusion.

`Compact/Geometry/C1092WindmillGap.lean` proves this as `no_wall`. It uses
full foreign squares, the original wall marker, containment and convexity.
It neither derives nor assumes extra auxiliary point ownership by q.

## What this does and does not settle

The root's independent exact arithmetic diagnostic in
`evidence/c1092-eight-square-diagnostic.json` checks the fixed model
`a=1001/1000`: the eight original marker codes, all 28 square-pair
separations, containment, and avoidance of all 48 wall targets and four
corner points by the closed central squares. That diagnostic supports the
countermodel; it is not a verification of the new continuum proof.

The new theorem closes the whole continuum of missing-wall placements for
these prescribed axis-parallel blockers. It explains a concrete geometric
constraint lost by the point relaxation. However, those blocker positions
are not established for an arbitrary original C1092 packing. In particular,
the original corner-pair owners can translate and rotate while retaining
their original markers. Full-length covered cuts are stronger than their
forced corner points. The arbitrary mppm sector therefore remains open.
The original entrance also retains all sixteen wall-center signs; no D4
reduction or elimination of the other fifteen signs is asserted here.

The next missing mathematical step is a stable replacement for the three
covered cuts under the actual neighboring-square orientations and shifts,
or a coupled support-sum inequality that recovers their corridor capacity.
Replacing the blockers by their compulsory points does not suffice, as the
exact eight-square model already proves.
