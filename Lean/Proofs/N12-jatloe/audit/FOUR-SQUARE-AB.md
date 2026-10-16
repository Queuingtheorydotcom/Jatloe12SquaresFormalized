# A/B interaction and the stronger A forced point

This records a symbolic investigation in the original `OpenSquare` model.
The whole four-square contradiction is still open. All counterexample
calculations below use exact rational arithmetic; they are not numerical
search results or counterexamples to the full packing theorem.

## Essential original information

The archived template initializes each square by subtracting every other
owner's compulsory hull (`template_replay.py`: `v.subtract(pieces,
v.minkowski(h,k,F(1)))`). The six separately listed forbidden points alone
do not capture those premises. The square's compulsory vertices are closed
points; disjointness of open interiors still excludes the entire foreign
closed hull from its interior.

`ClosedPointExclusion.outside_of_closed` proves this boundary transfer by
interpolation toward the foreign center. `closed_segment` proves the closed
convexity needed for each foreign compulsory edge. The parent has checked
both lemmas in Lean.

## A/B and even A/B/L alone do not settle the geometry

The exact common-side triple in `four-square-abl-witness.json` has
`a=1001/1000` and:

| Square | c | s | loU | loV |
|---|---:|---:|---:|---:|
| A | 4/5 | 3/5 | 287/100 | -49/125 |
| B | 35/37 | 12/37 | 13999/7400 | 58973/37000 |
| L | 1 | 0 | 0 | 3799/2000 |

Each contains all its compulsory points strictly, excludes the six forbidden
points, and lies in the container. All three pairs are separated: the A/B
gap on A's V normal is `109819/6845000`, the A/L horizontal gap is `581/625`,
and the L/B gap on B's U normal is `77/18500`.
A and B have horizontal section widths `683/800` and `10903/12000` at
`y=12/5`, both below one. A contains R's compulsory point `(3,12/5)` strictly.
Thus genuine A/R information is essential; adding more B/L algebra alone
cannot repair this reduced implication.

## Two face modes suffice for substantial A progress

Write `U(x,y)=cx+sy`, `V(x,y)=-sx+cy`, and the square's lower faces as `u,v`.
For positive nonzero components, A's owned points imply that missing
`G=(47/20,33/20)` is below U or below V. The foreign B point
`B0=(33/20,47/20)` and foreign R point `R0=(3,12/5)` sharpen those alternatives:

1. `u>=U(G)` implies `v>=V(R0)`. To see this, own `(2,113/50)` first forces
   `.35c<=.61s`; R0 is then strictly between A's U faces and below its upper
   V face. Its exclusion therefore forces the lower V face.
2. `v>=V(G)` implies `u>=U(B0)`. B0 cannot fail upper V because
   `V(B0)-V(G)=.7(c+s)<=1<a`, and its other two non-lower-U faces are strict.

These modes gave the checked `FourSquareALower.lower_center`: A lies above
the lower limit of the conservative long-section radius. More directly,
they force A to contain `(2,5/2)` whenever `s+c/10<=1`:

* In mode 1, its upper-U gap is controlled by the vector `(-.35,.85)`, whose
  squared length is `.845<1`; its upper-V gap follows from `s+c/10<=1<a`.
* In mode 2, the corresponding upper-U vector is `(.35,.15)`, squared
  length `.145<1`, and the upper-V vector is again `(-.35,.85)`.
* The two lower faces follow strictly from the owned P/Q points.

`FourSquareAForced.lean` implements the original positive shallow sector and
an explicit axis branch; its final validation is owned by the parent. The
core argument only needs `s+c/10<=1`, which follows from `20s<=99c` and the
unit-normal equation. The still problematic orientations are therefore
confined to `0<c<(20/99)s`, rather than the whole complementary sector.

## Why the last orientation interval needs actual A/R geometry

`four-square-a-steep-hull-witness.json` gives an exact A square with

```
a = 1001/1000, c = 40/401, s = 399/401,
loU = 15047/8020, loV = -1101/401.
```

It contains A's three points strictly, excludes all six forbidden points,
and lies in the container. It avoids the entire B and L compulsory hulls
above its V band and the entire R hull below its V band. Nevertheless
`(2,5/2)` exceeds its upper V face by `1599/401000`.
No actual neighboring B/L/R squares are asserted in this example. It proves
only that point and hull exclusions alone cannot establish the final
orientation branch. Actual R disjointness together with the right wall is
a plausible next input. Reflection `x -> 4-x` turns R into the familiar
left-wall triangle `(.914,2),(1,2.26),(1,2.4)`, with missing point
`(.76,1.87)`; A becomes a square with a small positive angle and owned
points `(2,2.26),(1.74,2),(1.65,2.35)`.

## Retained alternative upper-center calculation

`FourSquareAUpper.lean` connects exclusion of B's entire compulsory segment
`(1.65,2.35)->(1.74,3)` to A's upper-center bound in the shallow sector.
With `gamma=.65s+.09c`, the segment-corner inequality is
`(.65c-.09s)u-gamma(v+a)>=.861`, yielding
`gamma*Y <= .439c+1.469s+a*gamma*(s-c)/2`.
The remaining high-angle inequality has a degree-six numerator with seven
positive Bernstein coefficients on one rational interval. These are exact
ring identities. This longer route is retained, but the direct forced
point is the current priority. Neither conditional route is a completed
four-square or global n=12 theorem.


## Subsequent completed all-orientation proof

The narrow-A interval and negative-B gap discussed in this earlier research
record are now closed. The all-orientation wall and A point arguments passed
Lean, and the negative-B two-point contradiction passed in6.895s+3.558s.
The complete shared four-square template passed in2.018s with only
`propext`, `Classical.choice`, and `Quot.sound`. See
`FOUR-SQUARE-NEGATIVE-B.md` for the final short negative-branch argument.
This is the complete local geometric theorem; its original case adapters
and classification coverage are separately checked obligations.
