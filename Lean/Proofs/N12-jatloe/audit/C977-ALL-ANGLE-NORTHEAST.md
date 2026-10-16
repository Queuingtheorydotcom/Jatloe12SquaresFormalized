# C977: one continuous northeast ending

11 October 2026. This records independently reviewed source, **not a Lean
acceptance receipt**. The final full-proof replay remains deferred.

`C977NortheastShift.all_frame_point` now proves that the actual northeast
paired owner contains `(3.5,3)` for every canonical sign of that owner
and its top and right neighbors. `right_shift_excludes` consequently
rules out the actual positive right-wall displacement. Its diagonal
counterpart `all_top_shift_excludes` rules out the top displacement.
Neither theorem assumes that both displacements happen together.

## Mathematical reduction

Write E for the genuine northeast paired square, T for the top wall
square, and R for the right wall square. They have their actual common
side greater than one, actual container boundaries, and disjoint interiors.
The original family supplies E's corner `(3,3)` and outward point
`(3.2,3)`, T's marker `(2,3.086)` and row point `(2.4,3)`, and R's
row point `(3,2.4)`. The original northwest central owner excludes
T's wing point `(1.74,3)`; the unused northeast marker excludes
`(2.35,2.35)` from T. No auxiliary vector is selected.

For positive E, the complete E/T separation proves E contains `(3.5,3)`
for either sign of T. For negative E, diagonal symmetry transports the
entire original packing and supplies E's vertical point `(3,3.5)`.
That point makes a hypothetical missing `(3.5,3)` select E's upper U
face. The complete E/T separation again rules out this face, with both
top-wall signs included. The last negative/negative sector uses only
unit-circle identities and continuous inequalities. Splits follow the
actual relative-angle sign and the two actual missing-wing faces.

Finally, a displaced R intersects the strict segment between E's
`(3.2,3)` and `(3.5,3)`. The witness is a point on R's actual row at
height 3. This contradiction does not depend on E's angle.

## Source and remaining obligations

- `UpperRightNegativePairReach` exhausts the last four separating axes;
  its two scalar helper modules prove every stated margin.
- `C977NortheastFarther.FrameData` binds all geometric premises once to
  the actual original owners. The negative/negative binding adds no
  packing assumption.
- `C977NortheastShift` performs the complete packing transport and joins
  every sign case. Parent and independent workers reviewed the support
  expansions, signs, polynomial identities, and original-owner bindings.

This removes a whole mathematical alternative in the center-owned
ending. Subsequent source now closes the positive steeper-neighbor and
transverse alternatives for either central sign, by direct use of the
original bottom crosspoint and farther bottom-wall point. It preserves
the missing-corner root without reflecting it. The negative-neighbor
continuation still remains; C977 is not yet excluded. See
[the current cap ending](C977-CENTRAL-CAP-ENDING.md).
