# Whole C981 representative 6: a continuous segment argument

Source checkpoint, 11 October 2026. The original `ExcludesVector` contract
for representative 6 is supplied by
`Compact.Bridge.C981DiagonalWallElbows.representative6_excluded` and is
connected to `Compact.Cases.C981Compact`. C981 has 47 whole-vector
obligations left. This is source completion, not Lean acceptance; compilation
remains deferred until the whole proof source is assembled.

In the actual chart `(x,y) = (4-oldY,oldX)`, central owner 5 contains
`(2,2.26)`, `(2.26,2)` and `(2.35,2.35)`. Right-wall owner 9 contains
`(3.086,2)`, `(3,2.4)` and `(2.4,3)`. Top-wall owner 10 contains
`(1.6,3)` and `(2.26,3)`. The existing opposite-elbow argument puts the
center `(2,2)` inside owner 7. It suffices to put that same center in owner 5.

The right wall owns the entire diagonal segment from `(3,2.4)` to
`(2.4,3)`. Convexity and the central square's two inner points therefore
exclude both `(2.5,3)` and `(3,2.5)` from the central square: each would
create intersecting segments of two disjoint squares.

Choose a positive face frame `(c,s)` for the central square. All angles
are included in three continuous ranges:

1. For `s <= c`, the existing full right-wall support argument applies,
   now with the stronger missing point supplied by the diagonal segment.
2. For `c <= s <= 2c`, a point of that same diagonal segment is chosen
   whose transverse coordinate equals that of `(2.35,2.35)`. If the center
   were missing, this point would lie strictly inside the central square.
   The needed longitudinal margin is
   `c+s-21/20-(7/10)cs > 0`, proved from the unit-circle identity and
   `4/3 <= c+s <= 10/7` by an exact polynomial inequality.
3. For `2c <= s`, the swapped half-angle crossing has coordinates
   `(2+z,3)`, with `z=c/(1+s)` between 0 and 1/4. That crossing lies in
   the actual top-wall segment from `(1.6,3)` to `(2.26,3)`, contradicting
   disjointness.

The argument uses the original side length, container, distinct owners,
exact marker ownership and exact auxiliary ownership. No hypothetical
top point `(2.4,3)` is assigned to the top wall: that point belongs to the
right wall in this vector. Source and original-entrance review passed.

The bounded literal applicability check inspected all 117 original rows
and found precisely representative 6 for this signature. It ran in 0.24
seconds; it is a diagnostic, not a replacement for the Lean `Check` proof.
The record is `evidence/c981-diagonal-wall-signature.json`, with resource
receipt `.verification/c981-diagonal-signature-20261011.json`.

No compiler, solver, pose search or ownership enumeration was run for this
closure. No claim is made here that the entire original C981 case is closed.
