# C981: exact auxiliary absence and the short top segment

Source status: the whole representative 3 exclusion is assembled and independently hand-reviewed. Lean replay is deferred. Representative 4 keeps its original public theorem statement and uses the same shared support cycle. The original finite-query signature diagnostic also matches representative 6, which already has an independent complete source route.

## The mathematical simplification

In the chart `new=(4-oldY,oldX)`, the inward northeast square A owns
`(2,2.26),(2.26,2),(2.35,2.35)`. Its exact auxiliary ownership excludes
`(2.4,3)` even when no other square owns that point. Therefore the narrow-angle and sharp right-wall clearance arguments need only this exact absence; they do not require a hypothetical top-wall owner of `(2.4,3)`.

`FullAuxWallEscape.narrow_faces_of_missing` and
`FullAuxWallRightSupport.original_bounds_of_missing` express precisely that fact. Their earlier foreign-owner interfaces are retained as corollaries.

For a positive steep frame `0<c≤s`, set `z=c/(1+s)`.

- If `z≥13/50`, A contains `(2.26,3)`. The center exclusion places its lower U face at or above `2(c+s)`, and the half-angle identity gives `.26c+s≤1`. The absent point `(3,2.4)` must lie below A's V interval. The vector from that point to `(2.26,3)` has squared length `.9076<1`, giving the remaining strict face bound.
- If `z≤13/50`, the exact half-angle crossing is `(2+z,3)`. It lies in the actual top square's strict segment from `(1.6,3)` to `(2.26,3)`.

Thus the whole steep sector closes through one strict segment, without top-square orientation subdivisions or a saved enclosure. The shallow sector uses the previously assembled complete A/C/B/L support cycle.

`C981FullAuxNegative.Check` checks all original point/absence premises, the independently proved opposite-center placement, and either the old top endpoint `(2.4,3)` or the new endpoint `(2.26,3)`. The new original theorem is `representative3_excluded`; no additional assumption appears in its statement.

## Exact remaining representative 2 obstacle

Representative 2 has the same common input data but its top owner owns only `(1.6,3),(1.74,3)` on that row. It does not satisfy the new top alternative. Its elbow itself excludes `(2.26,3)`, so the preceding endpoint argument still removes steep frames with `z≥13/50`.

The unresolved sector is `0<c<s` and `c/(1+s)<13/50`. A stronger top point must not be assumed. After swapping axes, the actual adjacent right-wall owner has the lower points `(3,1.6),(3,1.74)`, not `(3,2.4)`. This admits an additional transverse A/wall separating direction that the existing upper-wall reduction does not remove. Any completion must retain that actual direction together with the opposite central square, upper central square, and their genuine wall/corner neighbors. No whole representative 2 exclusion or point-only replacement is asserted.
