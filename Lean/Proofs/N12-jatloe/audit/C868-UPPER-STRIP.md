# C868: exact upper-strip bottleneck

This is a mathematical audit, not a completed exclusion or a Lean check. The
seven original-domain vectors are recorded in
`evidence/c868-nine-domains-diagnostic.json`. The original family is
`{1,2,12,16,192,256,512,3072,4096,8192,16416,32768}`.

## Actual retained points

The promising configuration consists of the actual squares E192, T32768,
C16, R16416 and H3072. Their compulsory strict points include:

| Square | Compulsory points |
| --- | --- |
| E192 | `(1,3.086)`, `(.914,3)`, corner seed `(1,3)` |
| T32768 | `(2,3.086)`, `(1.6,3)`, `(1.74,3)` |
| C16 | `(3,3.086)`, `(2.26,3)`, `(2.88,3)`, `(2.13,3.24)` |
| R16416 | `(3.086,2)`, `(3.086,3)`, `(3,2.25)`, `(3,2.75)`, `(3,2.26)`, `(3,2.4)` |
| H3072 | `(1.65,2.35)`, `(2.35,2.35)`, `(2,2.26)` |

H must exclude both actual A256 points `(2,1.74)` and `(1.74,2)`.
This is stronger than merely retaining its two original central markers.
The earlier endpoint template needs `(3,1.6)`, which is not globally owned
by the upper-right wall square in these vectors. That template is therefore
not an available adapter.

## Exact countermodels to dropping either lower crosspoint

These are hand-derived rational configurations. They are counterexamples to
weakened five-square statements, not to C868. They do not satisfy the omitted
foreign-point exclusion. No numerical search or Lean replay was run here.

All squares have side `a=1001/1000`. A row `(c,s,u,v)` means the original
square inequalities `u<c*x+s*y<u+a` and `v<−s*x+c*y<v+a`.
Use the following same four upper squares for both countermodels:

| Square | c | s | u | v |
| --- | --- | --- | --- | --- |
| E | 1 | 0 | 0 | 2999/1000 |
| T | 1 | 0 | 26/25 | 2999/1000 |
| C | 1 | 0 | 1039/500 | 2999/1000 |
| R | 4/5 | 3/5 | 7199/2000 | −901/2000 |

E, T and C have horizontal ranges `[0,1.001]`, `[1.04,2.041]` and
`[2.078,3.079]`, respectively, and vertical range `[2.999,4]`.
R has centre `(3.25,2.5)` and bounding box
`[2.5493,3.9507] × [1.7993,3.2007]`. Its upper V face is `.5505`,
whereas the minimum of V on C is `.5518`; their separating gap is `.0013`.
The other separations are horizontal. Each square contains all its points
listed above strictly and has the stated original marker mask.

First choose H axis aligned, with `u=1499/1000`, `v=1997/1000`.
It contains the three H points, excludes both lower central markers, and
excludes `(2,1.74)`. It **contains `(1.74,2)`**. Its top is `2.998`, below
E/T/C, and its right face is `2.5`, left of R. Thus keeping only the first
lower crosspoint exclusion does not suffice.

Next choose H with `(c,s)=(4/5,3/5)`, `u=324/125`, `v=−9/100`.
The two upper central markers have `(U,V)` values `(2.73,.89)` and
`(3.29,.47)`; `(2,2.26)` has `(2.956,.608)`. All are strict. The excluded
point `(1.74,2)` lies on the lower U face `2.592`; the lower-right central
marker lies on the lower V face `−.09`. But **`(2,1.74)` lies inside**.
H has bounding box `[1.527,2.9284] × [1.4832,2.8846]`. Its upper U face
`3.593` is below R's lower U face `3.5995`, so all five squares are disjoint.
Thus keeping only the other lower crosspoint exclusion does not suffice.

## The entire five-square upper-strip relaxation is feasible

Even imposing both lower crosspoint exclusions does not force H to contain
`(2,3)` or to overlap any of R's compulsory points. For example, the same
positive frame for H, now with `u=53/20=2.65`, `v=−9/100`, still contains
all H points and excludes both lower central markers and both crosspoints.
Its top is `2.9194`, and it excludes `(2,3)` and `(3,2.4)`.
Its right face reaches `2.9748`. This square conflicts with the particular
R above, but moving that actual wall square gives a complete five-square
countermodel even with both crosspoint exclusions. Replace R by
`(c,s,u,v)=(4/5,3/5,731/200,−9/20)`, retaining its side `1001/1000`.
Then:

* R's bounding box is `[2.5934,3.9948] × [1.833,3.2344]`, inside the box.
* Its original lower wall marker has `(U,V)=(3.6688,−.2516)`, and its upper
  wall marker has `(4.2688,.5484)`. Both are strict within
  `(3.655,4.656) × (−.45,.551)`.
* Both wall seeds and both forced auxiliary points remain strict.
* R is separated from C by V, with gap `.5518−.551=.0008`.
* R is separated from H by U, with gap `3.655−3.651=.004`.
* E/T/C remain above H, and E/T remain left of R.

The exact auxiliary signatures are E `{}`, T `{3,14}`, C `{7,17}`,
R `{9,19}`, H `{5,16}`. These match the second vector of the original
diagnostic. Every square retains its exact original marker mask. Thus the
whole five-square upper-strip statement is false, even with correct lower
crosspoint exclusions and genuine wall/corner square geometry. A complete
C868 proof must retain at least one additional actual square (for example
A256, lower-right B512 or the left wall L4096), beyond the points they own.
The parent has now independently checked all five unit normals, all vertex
containment, all exact marker/auxiliary signatures, every supplied strict
extra point, both H exclusions and all ten pairwise separating axes using
exact fractions. The successful receipt is
`evidence/c868-upper-five-exact-verification.json`. This remains a rational
diagnostic, not a Lean theorem or a counterexample to the original packing.

The available SouthwestNegativeCorner result cannot currently be used to
replace the two crosspoint exclusions by `H` missing `(2,2)`: the ordinary
singleton/elbow data do not force A256 to contain `(2,2)` for positive
canonical A. The exact obstruction is separately recorded in
`evidence/three-corner-positive-exact-aux-countermodel.json`.

## Small continuous reduction for T

For a canonical positive T frame `c>0`, `0≤s≤c`, exclusion of E's `(1,3)`
puts that point below T's U face or above its V face. Exclusion of C's
`(2.26,3)` puts that point above U or below V. The double transverse choice
would give `a≤1.26s<1` and is impossible. The choice E-above-V and C-above-U
forces T to contain H's `(1.65,2.35)`: the two lower-face gaps have vectors
`(.65,−.65)` and `(−.61,−.65)`, both shorter than one, and the upper faces
follow from T's original points. Hence that choice is impossible too.

The two surviving choices are:

1. E below U and C above U, giving `a≤1.26c` and therefore `c>50/63`.
2. E below U and C below V. The additional C point `(2.13,3.24)` must then
   be above T's U face. Its entire owned segment to `(2.26,3)` supplies a
   coupled constraint, rather than an independent point exclusion.

These are two continuous face sectors, not an angle enumeration. They
cannot close the five-square relaxation, because of the exact countermodel
above. The next route must add actual lower/left-square separation.
There is no new whole-case theorem or registry entry from this audit.

## Sixth-square sector now assembled in source

Retain the full lower-left A256, with strict southwest marker and its actual
foreign points `(1.6,1)` and `(1,1.6)`. For a positive canonical A frame
`(C,S)`, these give three alternatives:

1. `loU ≥ 1.6C+S`;
2. `loV ≥ 1.6C−S`, necessarily `13S<C`;
3. `loU ≥ C+1.6S` and `loV ≥ C−1.6S`.

`Compact/Geometry/C868CentralSupport.lean` contains the source proof of this
mode reduction and its support consequence
`upper A(c,s) > 1.65c+2.35s` for every positive canonical direction `(c,s)`.
The five margins now have explicit continuous cone proofs in
`C868CentralMargins.lean`; their earlier 49-pair diagnostic is superseded as
mathematical support by those source proofs. They have not been compiled.

The support bound removes both longitudinal separating axes. The two
remaining transverse alternatives force `H.Inside (1.74,3)`, using three
additional exact scalar inequalities in `C868UpperPointMargins.lean`.
This contradicts the actual top owner T32768's strict ownership of that
point. This is an entire orientation-sector contradiction, without a grid.

`Compact/Cases/C868/Ownership.lean` binds the required points to nine genuine
original domains. It uses existing checked combined specs, a transported
half-turn spec, and the right wall's actual seed segment with its full
two-point G budget. `ForcedAuxiliary.contains` proves individual memberships
without assuming A256's complete auxiliary set is constant across the seven
vectors. `Compact/Cases/C868/PositiveSector.lean` then proves the contradiction
for positive canonical frames of both A256 and H3072. These are source-only
claims pending Lean replay, not a new accepted whole case.

## Remaining actual orientation obligations

`C868UpperPointNegative.point` derives the same contradiction for negative A
and positive H **if A strictly contains `(2,2)`**. The original corner theorem
can supply this only when the actual bottom singleton excludes `(1,1)`.
That exclusion is not supplied by the nine-domain cover. In particular,
the fact that the left singleton then excludes the corner does not permit a
silent interchange of the physical central orientation. The full negative-A
branch therefore remains open.

There is a precise obstacle to removing the actual corner geometry. Write
A's frame as `(C,-T)` and H's as `(c,s)`, with both nonnegative pairs unit and
canonical. A's two missing auxiliary points give three face modes:

1. `loV ≥ T+1.6C`;
2. `loU ≥ 1.6C−T`, which forces `13T<C`;
3. `loU ≥ C−1.6T` and `loV ≥ 1.6T+C`.

The first mode forces A's centre point; the second has a strong small-angle
bound. The third is the coupled gap. With
`E = (cC−sT)−C+(sC+cT)(.09c+.65s)`, an attempted point-only closure would
need `E+1−C−.14T ≥ 0`. At the valid H axis `(c,s)=(1,0)` this is
`1−C−T/20`, which is negative at the exact unit normal
`C=1599/1601`, `T=80/1601`: its value is `−2/1601`.
Thus this proposed scalar bound is false. It must be strengthened with an
actual neighbouring square, not admitted or certified from a sampled grid.

Negative canonical H is also still open. Reflecting the packing horizontally
would exchange the strong lower-left triangle with B512, whose genuine
points differ: its F point is `(3,1.74)`, and its G point can be `(3,1.6)`.
Consequently that reflection does not supply the lower-left triangle required
by the positive-H theorem. No whole C868 registry entry has been added.
