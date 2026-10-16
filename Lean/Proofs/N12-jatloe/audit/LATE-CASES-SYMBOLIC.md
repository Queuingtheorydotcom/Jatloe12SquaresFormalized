# Symbolic entrance audit of the other six historical exclusions

Status: source-only audit. The recovered historical proofs remain the full
reference exclusions. This note does not claim six new compact proofs.
No Lean, numerical solver, or propagation generator was run for this audit.

## Exact original differences

The records inspected are `evidence/historical/data/case<ID>-input.json` for
701, 713, 717, 973, 978, and 979. The original final statements were also read
from the authenticated compressed `Push<ID>Chunk*.lean.gz` source, without
extracting their generated numerical declarations.

| Case | Central marker structure | Direct obstacle to the four-square template |
|---|---|---|
|701|Mask1536 owns both right central markers9,10; mask34816 owns11,15|The candidate A owns its supposedly missing lower marker; the upper B owns its supposedly missing top marker15|
|713|Mask2304 owns both left central markers8,11; marker10 is unused|The central triangle is replaced by a vertical pair; existing template needs distinct upper/lower owners|
|717|Mask768 owns bottom pair8,9; mask3072 owns top pair10,11|Both central owners are bars rather than the template's single-marker triangles|
|973|Central markers8,9,10,11 have separate owners; marker13 is unused|The right central owners have no common auxiliary triangle at entry; their certified domains retain many alternatives|
|978|Mask33792 owns10,15; markers8,9,11 have separate owners|The putative A also owns top marker15, and its common entrance has only those two points|
|979|Mask3072 owns top central pair10,11|An upper horizontal bar replaces the template's separate A/B; the top-wall owner has only marker15 in the common entrance|

The original common hulls are conclusions of their ownership-domain proofs.
They must not be inserted as unconditional hypotheses in new case adapters.
In particular, an auxiliary point absent from a common hull can still belong
to some retained owner alternative. This affects the missing inward points
needed by the wall-point theorem, not merely the strength of a numeric bound.

## A genuinely shared new geometric consequence

`Compact/Geometry/CentralPairPoint.lean` proves the following in the unchanged
`OpenSquare` model. Parent replay passed in 1.974 seconds with only the
standard Lean axioms:

> Side>1, both closed top central markers `(1.65,2.35),(2.35,2.35)`, and
> absence of both bottom central markers imply strict membership of `(2,2.5)`.

The proof uses no auxiliary ownership or enclosure. Choose a canonical face
frame with `c>0`, `|s|<=c`. The top pair immediately brackets the target's U
coordinate and bounds its lower V coordinate. If the target were above the
upper V face, the two top constraints give `|7s|<=3c`. Both lower central
markers are then strictly inside the V strip: their differences to the
target are `(±0.35,0.85)`, with squared length169/200<1. Their U coordinates
are separated by only0.7c<1, so a U strip of width>1 must contain one of them.
That contradicts the exact missing-marker premise.

This is an all-angle consequence, including canonical boundary orientations.
It derives a strict point from closed anchors; it does not identify closed
hull membership with open interior membership.

Its D4 images apply to the following original masks without any additional
auxiliary-domain refinement:

| Case | Mask / owner position in original input | Forced point |
|---|---|---|
|701|1536 /7|(2.5,2)|
|713|2304 /7|(1.5,2)|
|717|3072 /7|(2,2.5)|
|717|768 /6|(2,1.5)|
|979|3072 /7|(2,2.5)|
|898|768 /5|(2,1.5)|

The transformed mask/point adapters have not been added merely to inflate
coverage counts. None of these new points alone proves an entire late-case
contradiction.

## Where the whole-case gap now lies

For C898, the earlier row reduction forces three occupied points at y=2.5.
The new central-pair lemma additionally places its bottom central owner at
(2,1.5). Neither fact establishes the fourth long section or the coupled
separation contradiction. Assuming that section would be circular.

The retained original geometric traces have31 steps for701,10 for713,19
for717,28 for973,16 for978, and30 for979. These counts include chord and other
pruning forms; they are not all ordinary pair steps. Their terminal empty
owners are respectively3,8,6,10,11,4 in the original input ordering. The
smallest dependency graph among these is713, involving original owners
0,1,5,6,7,8,9,10,11. It is the most focused next symbolic target: combine the
new left central point with the actual left-wall and corner owners to rule
out owner8. The existing proof still uses two corner/wall updates and a
central coupling; no replacement inequality for that complete interaction
has been derived here.

No honest source-size bound below300,000 for all historical successes follows
from these local consequences yet. A new whole coupled lemma, or exact
cross-case sharing of the recovered certificate objects, remains necessary.

## Case713: exact next reduction and its limit

The authenticated final theorem uses original owners
`[0,1,5,6,7,8,9,10,11]`. Its step5 is a **horizontal window-chord** update of
owner7, with owners1,6,10 as its three neighbors. It is not an ordinary
pair update. The final empty owner is8, after comparison with the updated
upper-left corner5 and central-left owner7.

There is already a symbolic entry to this chord step: original owners1,6,10
contain respectively `(1,87/50)`, `(2,87/50)`, `(3,87/50)` in the original
common hulls. These closed points, actual disjointness, and containment in
the container exclude a long horizontal section of owner7 at `87/50`.
No preceding pruning state is needed for that particular conclusion.

In a canonical frame write `c>0`, `z=|s|`, and
`rho=(c+z-2*c*z)/2`. Owner7's top marker at height `47/20` gives
`centerY >= 47/20 - a*(c+z)/2`. Since `a<=1001/1000`, `c+z<=10/7`, and
`c*z<=1/2`, this is strictly greater than `87/50-rho`: the remaining
margin is at least `61/100 - 1/1400 - 1/2 > 0`.
The checked long-section theorem and the excluded section therefore imply
`centerY > 87/50+rho`. The reusable all-angle theorem is now assembled in
`Compact/Geometry/CentralBarHeight.lean`, pending parent replay. Its public
`from_three_occupied_points` allows any upper compulsory point at least
`51/100` above the blocked row. The exact Case713 packing adapter has not
yet been written or replayed.

### A tempting stronger local conclusion is false

Owning both top central markers and excluding both bottom central markers
and the inward point `(2,87/50)` does **not** force a long section at `5/2`.
An exact single-square witness is

```
c = 4/5, s = 3/5, side = 1001/1000,
loU = 529/200, loV = -89/1000.
```

Its top-marker projections are `(273/100,89/100)` and
`(329/100,47/100)`, strictly inside both bands. The bottom-left marker has
U coordinate `231/100 < loU`; the bottom-right marker has V coordinate
`-9/100 < loV`; the inward point has U coordinate `661/250 < loU`.
The point `(2,5/2)` is inside, as the checked CentralPairPoint lemma predicts.
All four vertices lie in the container. But its horizontal section at `5/2`
is exactly the interval `(136/75,1073/400)`, of length `1043/1200 < 1`.

This is a counterexample only to the proposed **local implication**, not a
legal full Case713 packing. Under the quarter-turn taking the top pair to
the left pair, it uses the still-allowed owner7/F5 branch. It explains why
the new forced point cannot simply replace all subsequent pair coupling.

### A valid angle restriction from an actual neighboring segment

One of Case713's complete ownership branches assigns F5=`(2,113/50)` to
owner7. Let Q be that owner and A the central-right owner6. The original
entry supplies strict Q points

```
P=(33/20,33/20), D=(2,113/50)
```

and closed A points `E=(2,87/50)`, `M=(113/50,2)`.
These alone, with disjointness, rule out a Q frame satisfying
`c>0` and `0<=s<=c/2`.

Indeed, put `t=17*s/(50*c)` and `H=(2+t,87/50+t)`.
Then H belongs to segment E--M with weight `17*s/(13*c)` in `[0,17/26]`.
For the U and V face coordinates of Q, direct algebra gives

```
U(H)-U(P) = (7/20+t)*c + (9/100+t)*s > 0,
U(D)-U(H) = s*(9*c-17*s)/(50*c) >= 0,
V(H)-V(P) = (c-2*s)*(9*c+17*s)/(100*c) >= 0,
V(D)-V(H) = (13/25)*c - t*(c-s) > 0.
```

Thus H is strictly inside Q and closed inside A, contradicting actual
disjointness. This argument uses no side bound, angle grid, numerical
enclosure, or unsupported conversion from closed anchors to strict points.
Strictness comes from Q's **actual owned** P and D. The algebraic argument is
now assembled in `Compact/Geometry/CentralSegmentAngle.lean`, with public
theorems `exclude_small_nonnegative` and `angle_gap`, pending parent replay.

Consequently this branch has `s<0` or `s>c/2` in a canonical frame.
The other ownership branches and the remaining coupling with owners1,5,8,11
still need a whole contradiction. No full Case713 exclusion is claimed here.

### The other ownership branch is steep in either sign

If owner7 does not own F5, it also cannot have a long section at `113/50`.
The three occupied positions on that row belong to original owner8 at x=1,
the actual F5 owner (6 or11 in the original complete domains) at x=2, and
original owner4 at x=3. All three are distinct from owner7. Its lower marker
at `33/20` is `61/100` below that row. Applying the reflected height argument
therefore gives

```
87/50 + rho < centerY < 113/50 - rho,
rho < 13/50.
```

For a canonical frame this implies `|s|>c/2`. To see the exact algebra, put
`c=|normalX|`, `s=|normalY|`, and assume `s<=c/2`. Then
`(2c-s)(c-2s)>=0` and `c^2+s^2=1` give `(c+s)^2<=9/5`, hence
`c+s<=27/20`. The product
`(27/20-c-s)*(c+s+7/20)>=0` bounds `(c+s)^2-(c+s)<=189/400`, whereas
`rho<13/50` requires that expression to exceed `12/25=192/400`.

These deductions are assembled in `Compact/Geometry/CentralBarTwoRows.lean`,
pending parent replay. Together with the strict-segment argument above, they
exclude the entire canonical interval `0<=s<=c/2` in **every** Case713
ownership branch. They do not exclude the remaining negative angles, or the
steep positive angles, and therefore do not constitute the case theorem.

The direct lower occupied row is also present in the inspected common hulls
for cases701,717,978,979: its three original owners are respectively
`(1,6,10)`, `(1,6,10)`, `(1,5,6)`, `(1,5,6)`. Thus the same height theorem
applies to any distinct upper central owner there. Case973's common entrance
does not supply the third point `(3,87/50)`, so this transfer cannot be made
uniformly to973 without additional ownership refinement.
