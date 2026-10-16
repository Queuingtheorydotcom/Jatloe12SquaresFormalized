# The positive 849/851 endgame needs a fourth owner

This is a fixed rational counterexample to a proposed *local* implication,
not a packing of all twelve squares and not a Lean case exclusion. It was
derived algebraically without a search. The accompanying tiny exact-arithmetic
checker is source only; this worker has not run it or a Lean compiler.

Set `a=1001/1000`, `c=209/241`, `s=120/241`. For the original open-square
coordinates `U=c*x+s*y`, `V=-s*x+c*y`, define

```
L.loV = 29963/24100
L.loU = (120/209)*(L.loV+a)
B.loU = L.loU+a
B.loV = 565/482
```

Both L and B have frame `(c,s)` and side `a`. The third square C is
axis aligned with x interval `(417/200,1543/500)` and y interval
`(2999/1000,4)`. Its side is also `a`.

The following original points are strictly owned:

| Square | Points |
| --- | --- |
| L | `(.914,2)`, `(1,2.26)`, `(1,2.4)` |
| B | `(1.65,2.35)`, `(1.6,3)`, `(1.74,3)`, `(2,3.086)` |
| C | `(2.26,3)`, `(2.13,3.24)`, `(2.88,3)`, `(3,3.086)` |

L excludes `(.76,1.87)` and `(1.65,1.65)`. B excludes the already forced
foreign points `(2,2.5)` and `(1,2.4)`, and the upper-left marker `(1,3.086)`.
C excludes `(3.086,3)` and B's marker `(2,3.086)`. All three squares lie
in the actual `[0,4]^2` container.

Their interiors are pairwise disjoint. L and B meet only along a U face.
The gap between B's maximum U and C's minimum B-U projection is exactly

```
546547/50369000 > 0.
```

L's maximum x is `a*(c+s)<417/200`, so L and C are separated as well.
The witness also satisfies the new necessary reductions:

```
B.loU+a <= 2.26c+3s
B.loV = -2s+2.5c
B.Inside (1.4,2.5)
L.Inside (1,2.83)
c+2.83s <= B.loU.
```

Therefore the B/L/C triples, their actual walls, their stated owned and
missing points, and these derived face bounds cannot finish the positive
branch. The next genuine coupling is the upper-left corner owner: owner4
in both cases, mask192 (markers6 and7), with original owned points
`(.914,3)`, `(1,3)`, `(1,3.086)`. That fourth square is absent from this
counterexample. It cannot be replaced by one of its center points or by an
unproved support inequality.

The exact-input provenance is
`evidence/historical/data/case849-input.json.gz` and `case851-input.json.gz`.
The verification script is `scripts/check_c849_positive_triplet.py`; its
assertions explicitly distinguish the local witness from a complete packing.

## Stronger fourth-owner test

The script also contains a second fixed rational candidate retaining the
entire upper-left square E, and therefore its actual exclusion of `(1,3)`
from B. Set `c=903/1145`, `s=704/1145`, keep `a=1001/1000`, and use

```
L = (0,a) × (1.87,1.87+a)
E = (0,a) × (4-a,4)
B.loU = c*a+s*(1.87+a)
B.loV = -2s+2.5c
C.loV = 3c-3.086s
C.loU = (4-c*(C.loV+a))/s-a
```

B and C share frame `(c,s)`. The candidate has six explicit separating
inequalities, one for each pair: L/B and B/C longitudinally in B's frame,
B/E transversely in B's frame, L/E vertically, and L/C and E/C horizontally.
It lies in the remaining sector `C.loV=V_C(3.086,3)`. The checker explicitly
checks every listed anchor and exclusion for all four actual squares.

This second candidate has not been run by this worker. If its exact
assertions pass, a whole 849/851 proof must retain more of A/R than just
their forced points `(2,2.5)` and `(3,2.5)`. In particular, A's compulsory
triangle and missing lower central markers constrain its full support,
which a single forced point cannot replace.

## New source-only sector proof

`Compact/Geometry/C849PositiveAbove.lean` now contains the complete
opposite C sector argument. Its dependencies prove an all-orientation
two-point cover of L, the necessary B/L face bounds, and both longitudinal
support contradictions using the actual upper-left marker `(1,3)`.
The statement still has the explicit `above` face hypothesis for C and
does not claim either original whole-case exclusion. No Lean replay of
these new modules has been run.
