# Rejected three-square center claim

The proposed `SouthwestCornerClosure.PositiveClaim` is false. It must not be
treated as a remaining lemma in the completion skeleton. Its source and the
conditional whole-case adapter were never compiled or registered. They have
been removed from `Compact/` and retained as text only in
`evidence/retired/C696FalseCornerClaim/` for the record.

The root's exact rational check in
`evidence/three-corner-positive-exact-aux-countermodel.json` verifies a complete
three-square counterexample with the actual marker codes 1, 2 and 256, exact
auxiliary assignments `{2,12}`, `{0,10}` and `{4,13}`, original singleton seeds,
both additional central crosspoints, congruence, containment, the side cap and
all three pairwise separating axes. The central square misses `(2,2)`.
Adding the two foreign auxiliary exclusions to the earlier contract therefore
does not repair it.

The completed negative-central geometry and its original C696/C977 sector
adapters are unchanged. A valid whole ending must use another actual square
or the coupling between the two opposite central owners. In particular one
cannot assume that every central owner individually contains the center.

The exact role map remains useful for an eventual stronger argument:

| Frame | Bottom singleton | Left singleton | Central owner | Adjacent left wall |
| --- | --- | --- | --- | --- |
| identity | 0 | 1 | 6 | 8 |
| diagonal | 1 | 0 | 6 | 9 |
| half-turn | 3 | 4 | 7 | 10 |
| half-turn and diagonal | 4 | 3 | 7 | 11 |

Each transformed central has the southwest triangle, the two strict extra
crosspoints `(2,1.5)` and `(1.5,2)`, and the exact original auxiliary exclusions.
This role identity is not an exclusion of the whole configuration.

## Opposite central coupling alone does not repair the statement

The same exact three-square example can be placed together with its
half-turn about `(2,2)`. This supplies all six actual roles 0, 1, 6, 3, 4,
7 with the corresponding reflected marker and auxiliary assignments. This
is a hand-checked consequence of the already recorded rational vertices,
not a new computational search or a twelve-square packing.

Write the three original squares as O, L, A. Their closed coordinate bounds
from the vertex record are contained in the following slightly larger boxes:

| Square | x range | y range |
| --- | --- | --- |
| O | `(0.9,2.23)` | `[0,1.31)` |
| L | `[0,1.1)` | `(0.89,2)` |
| A | `(0.96,2.07)` | `(1.26,2.36)` |

Reflecting gives O' in `(1.77,3.1) × (2.69,4]`, L' in
`(2.9,4] × (2,3.11)`, and A' in `(1.93,3.04) × (1.64,2.74)`.
Every cross-triple pair except A/A' has a strict coordinate gap:
O against O'/A' separates in y, O against L' in x; L against all three
separates in x; A against O' separates in y and against L' in x.

For A/A' the actual normal is `(399/401,40/401)` and

    A.loU + A.side = 878/401 = 2*(A.c+A.s).

The reflected square's lower support in the same normal equals this value.
Thus their open interiors are disjoint even though both miss the center on
the common support line. No implication based only on these six complete
squares and their stated individual assignments can force central overlap.
The four actual wall owners, or another genuinely additional original
packing constraint, must enter the final argument.
