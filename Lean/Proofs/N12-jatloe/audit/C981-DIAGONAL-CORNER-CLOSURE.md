# C981 diagonal wall and genuine corner

Source-only checkpoint. No compilation or numerical search was run for
this argument. The three original-vector adapter proofs are assembled in
`Compact/Bridge/C981DiagonalCornerElbows.lean`; their finite entrance checks
and complete dependency closure still require Lean replay.

The same all-angle theorem handles original representative rows 5, 6 and
42. In the chart `old=(new_y,4-new_x)`, the central elbow is owner 5 and
the diagonal wall is owner 9. Owner 2's genuine paired-corner seed supplies
the foreign point `(3,3)`. The opposite owner 7 already contains `(2,2)`
by the unchanged `C981DoubleWallElbows` placement 2.

The new mathematical reduction is in `DiagonalWallCenter`:

1. Write the diagonal wall in a canonical frame `(d,r)`. It strictly owns
   `(3.086,2)`, `(3,2.4)` and `(2.4,3)`, and misses `(3,3)`.
2. If `r≥0`, the missing corner forces the upper U face below `3(d+r)`.
   The marker implies `.086d<r`, whereas the marker-to-top V width gives
   `d+.686r<1.001`. Their squared inequalities contradict the unit normal.
3. Thus its frame is `(d,-t)`. The same two points now give
   `.686d+t<1.001`, forcing `2t<d` continuously.
4. Existing shared arguments already handle a shallow elbow and the
   middle positive sector. In the remaining sector, reindex the elbow's
   frame to `(s,-c)`, where `2c<s`.
5. The actual elbow owns both outer points `(2.65,2.35)` and `(2.35,2.65)`.
   On either negative U axis, the first outer point projects beyond the
   wall's `(2.4,3)`, while the wall marker projects beyond the elbow's
   `(2.26,2)`. On either V axis, the second outer point projects beyond
   the marker because `.65d-.736t>0`; the wall's top point projects beyond
   the elbow's inner point. Every one of the eight separating alternatives
   is impossible.

Therefore both original central owners strictly contain `(2,2)`, contrary
to their actual disjointness. No top-wall auxiliary assumption is used;
in particular the proof does not insert the unavailable `(2.26,3)` into
representative 5's top owner. The original side cap `1001/1000` is retained.
