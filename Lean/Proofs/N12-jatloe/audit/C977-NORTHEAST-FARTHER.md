# C977 northeast paired corner: farther reach

## Validation boundary

The following is a continuous source proof, independently reviewed by
`positive_central` and `ending_c977`. No new Lean compilation or numerical
search was run for this result. It is a whole geometric sector and an
original-packing adapter, not a whole C977 exclusion.

## Actual geometric statement

Let `E` be the actual northeast paired corner and `T` the actual top wall,
with equal side greater than one and full interior disjointness. Assume
`E` has positive canonical normal. The proof retains:

- `E` is in the container and owns `(3,3)` and `(3.2,3)`.
- `E` misses the actual right-wall point `(3,2.4)`.
- `T` is in the container, owns `(2,3.086)` and `(2.4,3)`, and misses
  `(1.74,3)` and `(2.35,2.35)`.

Then `E` strictly contains `(3.5,3)`, for either canonical sign of `T`.
The right-wall exclusion is essential: a hand-derived equal-diagonal
two-square relaxation satisfies the other listed data while missing the
target, but wrongly owns `(3,2.4)`. That diagnostic was not a new exact
computationally checked witness and is not used in the proof.

## Continuous mechanism

Write the corner normal as `(e,f)`. If the target is absent, its only
possible faces are

`E.hiU <= 3.5e + 3f` or `E.loV >= 3e - 3.5f`.

The foreign right-wall point also forces
`E.loV >= 2.4e - 3f`; the competing longitudinal escape would leave side
at most `.5e + .6f < 1`. This removes the entire corner-transverse
separating axis. Strict original anchors direct both longitudinal axes
from `T` toward `E`.

For positive `T=(c,s)`, its two missing points give the uniform full-face
bound `T.loU >= 1.7c + 3s`. The corner-owned longitudinal axis is removed
by the stronger full-square support inequality

`upper(T,(e,f)) + side > 3.5e + 3.6f`.

The proof retains every missing-point face and relative-angle sign.
Its scalar margins use unit-circle identities, two broad arc estimates,
and one quartic endpoint-chord certificate. No angle list is used.

For the top-owned longitudinal axis, let `K=ec+fs` and `H=es-fc`.
The upper-U target escape is excluded directly by the uniform lower face.
For the lower-V escape, the actual top boundary of `E` cancels both
translation variables. The two resulting nonnegative margins are

`f(1-.8c) + K(e+f-1)` when `H>=0`, and

`c(1-e) + f[(1-s)+c(e-.8)+fs]` when `H<=0`.

The remaining top-transverse axis is removed by the foreign right-point
floor and the same target-face alternatives.

For negative `T=(c,-s)`, its missing northeast marker and wing force
`T.loV >= 2.35(c+s)`, together with the exhaustive wing alternatives
`T.loU >= 1.74c-3s` or `T.loV >= 3c+1.74s`.
The actual top boundary is retained in the second alternative. Six short
unit-circle margins exclude the two longitudinal selectors; the strict
corner/row anchors and complete side exclude both transverse selectors.

## Source and original ownership

- `UpperRightCornerReachAxes.lean`: target faces and complete SAT reduction.
- `UpperRightCornerLongitudinal{Norm,Bounds,}.lean`: positive-top support
  surplus and corner-owned longitudinal exclusion.
- `UpperRightCornerTopTransverse.lean`: positive-top transverse exclusion.
- `UpperRightCornerTopLongitudinal.lean`: final positive/positive point.
- `UpperRightNegativeTop{Bounds,Reach}.lean`: complete opposite-sign point.
- `C977NortheastFarther.frame_point`: actual owner `3`, with owner `10`
  supplying `(3,2.4)`, owner `11` supplying top marker/row, and owner `7`
  supplying `(1.74,3)`. The unused marker supplies the northeast exclusion.

`C977NortheastFarther.right_shift_excludes` combines this point with the
actual right-wall row-edge argument: a positive right wall cannot have
`R.loU >= 3R.c + 2R.s` when the corner frame is positive.

`C977NortheastShift.top_shift_excludes` transports the entire original
packing by the diagonal swap. It excludes the corresponding top shift
when the corner frame is negative. `simultaneous_excludes` covers both
corner signs if both shifts hold. The current global either-wall escape
does not supply both shifts; the opposite orientation/escape cells remain
separate obligations.
