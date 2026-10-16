# Rows 35 and 60: outer-top elbow beside the diagonal wall

Source-complete mathematical argument; Lean replay has not been run.

The common chart maps `(x,y)` to original coordinates `(y,4-x)`.
Actual owner 5 owns `(2,2.26)`, `(2.26,3)`, and `(2.35,2.35)`.
It excludes the northwest marker `(1.65,2.35)`. Owner 9 owns
`(3.086,2)`, `(3,2.4)`, and `(2.4,3)`. The actual paired owner 2 owns
`(3,3)` in this chart; this corner is obtained from its original seed,
not presumed to appear in owner 9's outside-query list. Actual owner 10
owns `(1.74,3)`.

The existing diagonal-wall lemma uses the genuine side bound
`side ≤ 1001/1000` and the foreign corner to choose the wall frame
`(d,-t)` with `0<t<d/2`. For every positive elbow frame `(c,s)`,
five directed SAT alternatives are removed using strict owned points.
Only elbow upper U, elbow lower V, or wall lower U can remain.

For `s≤c`, the center's absence implies a lower U or lower V face.
In the latter case, the genuine absent northwest marker forces the
stronger lower U face at that marker. Closed square corners give exact
support lower bounds in either branch. The shared unit-circle margins
in `DiagonalOuterElbowBounds` eliminate both longitudinal alternatives;
the elbow lower-V alternative already contradicts the diagonal point.

For `c≤s`, the center can escape only below U. The top owner's point
`(1.74,3)` then forces the elbow's upper V face below that point.
The opposite V separator leaves width at most `.66s<1`. For the wall-U
separator, use the elbow's closed lower-V edge at the U coordinate of
its actual `(2.26,3)` point. Its projection exceeds the wall's actual
diagonal point by

`d*(s-.52*s^2-.14) + t*c*(1-.52*s) > 0`.

This argument handles the sign of `dc-ts` without assuming it positive.
Thus the entire angle circle forces owner 5 to own the center. The
unchanged opposite-elbow placement 2 forces actual owner 7 to own it
as well, contradicting original pairwise disjointness. Both original
rows share this exact entrance; row 60's additional owner-7 auxiliary
is unnecessary.

New source: `Compact/Geometry/DiagonalOuterElbow.lean` and
`Compact/Bridge/C981DiagonalOuterElbows.lean`. Finite membership proofs
and geometric proofs remain ordinary kernel proof obligations, pending
the parent-controlled replay. No numerical search or local build was run.
