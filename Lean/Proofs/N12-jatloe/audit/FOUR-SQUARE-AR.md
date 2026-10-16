# A/R alone does not imply the four-square long-section conclusion

This is an exact counterexample to the proposed reduction using only A, R,
their compulsory points, all six excluded points, containment, and disjointness.
It is not a counterexample to the full four-square statement: the missing A/B
interaction is essential.

Set the common side to `a=1001/1000`. Give A center `(21/10,21/10)` and axes
`(c,s)=(4/5,3/5)`. Give R center `(17/5,12/5)` and axes `(1,0)`.
In the original OpenSquare representation:

| Square | loU | loV | c | s |
|---|---:|---:|---:|---:|
| A | 4879/2000 | -161/2000 | 4/5 | 3/5 |
| R | 5799/2000 | 3799/2000 | 1 | 0 |

Both squares lie in `[0,4]²`. A's rightmost x-coordinate is `28007/10000`,
strictly below R's left face `5799/2000`; hence their interiors are disjoint.
A strictly contains `(47/20,47/20),(2,113/50),(113/50,2)`.
R strictly contains `(1543/500,2),(3,113/50),(3,12/5)`.

For completeness, the following table gives each excluded point's A/R face
coordinates relative to that square's center. A point is excluded if either
coordinate has absolute value at least `1001/2000`.

| Square | Excluded point | u offset | v offset |
|---|---|---:|---:|
| A | (1,1543/500) | -721/2500 | 1811/1250 |
| A | (33/20,33/20) | -63/100 | -9/100 |
| A | (47/20,33/20) | -7/100 | -51/100 |
| A | (2,1543/500) | 1279/2500 | 1061/1250 |
| A | (19/25,187/100) | -121/100 | 31/50 |
| A | (81/25,187/100) | 387/500 | -217/250 |
| R | (1,1543/500) | -12/5 | 343/500 |
| R | (33/20,33/20) | -7/4 | -3/4 |
| R | (47/20,33/20) | -21/20 | -3/4 |
| R | (2,1543/500) | -7/5 | 343/500 |
| R | (19/25,187/100) | -66/25 | -53/100 |
| R | (81/25,187/100) | -4/25 | -53/100 |

At `y=12/5`, A's actual open horizontal section has relative x-coordinate
interval `(-521/1200, 641/1600)`. Its width is exactly `4007/4800<1`.
Also its unit-side conservative chord radius is `11/50`, while the height
difference is `3/10`. Thus neither the actual long section nor the proposed
radius interface follows from these reduced premises.

All listed inequalities were checked by direct Python Fraction arithmetic
(no search, angle enumeration, Lean compilation, or numerical approximation).
The example was also derived directly by inspecting the two face coordinates.
A formal counterexample theorem has not been added; its role is to reject an
invalid simplification before spending proof effort on it.
