# Further original-family review after the first 35 adapters

Source-only review. No Lean run, geometric search, or certificate generation
was performed. The parent reported that the independent finite ownership
audit passed all nine convex-entry cases, with at most 66 search nodes per
case. That diagnostic is not Lean acceptance.

## Two complete routes missed by the point screen

Cases 841 and 842 fit the existing lower-barrier four-square theorem.
The saved point screen reported that B lacked the exclusion of
`(2,1543/500)`. This is marker15, listed as globally unused in both original
rows. Since B's exact marker mask is2048, `ExactMarkers` proves the exclusion
directly; foreign ownership is unnecessary.

In original owner order the five selected owners are A7, B8, L9, R11,
and foreign owner6. Their masks are
`1024,2048,4096,16384,512` for841 and
`1024,2048,4096,16416,512` for842.
The foreign512 owner supplies R's missing point `(3,87/50)` by actual
disjointness. The actual singleton mask2 supplies L's lower missing point.
All F/G budgets have exactly two exemptions. In842 the right wall seeds
`(3,9/4),(3,11/4)` supply `(3,12/5)` by weight3/10, using the existing
checked convex certificate bridge.

Concrete original-family and `ExcludesCase` bindings are assembled in
`Compact/Cases/FourSquareUnused/` and
`Compact/Assembly/FourSquareUnusedCases.lean`. They are frozen for parent
replay. Their tiny ownership diagnostic is
`audit/check_four_square_unused_domains.py`; no run is claimed here.

The point screen should include every marker outside an owner's exact
mask, including globally unused markers. Its recorded outside lists alone
omit these valid exclusions. The same issue explains its reported gap for
the already covered case78. The screening worker has been notified.

## The adjacent family has a genuine missing premise

Cases849 and851 differ substantially: B's actual mask is34816, containing
both marker11 `(1.65,2.35)` and marker15 `(2,3.086)`. Thus B strictly owns
the very point that the current four-square endgame requires it to exclude.
Replacing that premise with a claimed unused-marker exclusion would be
false. The original input also supplies B's F3 point `(1.6,3)`; convexity
supplies G4 `(1.74,3)` from the recorded compulsory triangle.

The same actual A, L and R arguments still give the two useful conclusions:
A strictly contains `(2,2.5)` and `(2,2.4)`, and B has no long section on
`y=2.4` because L,A,R occupy its three available integer slots.
These conclusions alone do not finish the case. The next genuine
interaction is with the additional top-right singleton mask16, which owns
`(2.13,3.24),(2.26,3),(2.88,3),(3,3.086)` and is disjoint from B and A.
One must prove a new joint implication from these actual data, or retain a
small verified enclosure argument. No full replacement is claimed.

## Why the merged central-pair cases are a different problem

Cases48,573,574 have a central-right owner of mask1536. It owns both
`(2.35,1.65)` and `(2.35,2.35)`, together with `(2.26,2)` in the proposed
refined entrance. The first point is another exclusion required by the
current A theorem, so merely changing the owner labels cannot apply it.
Their recorded F/G domains also allow multiple sets and must be derived
from the original budgets before any per-assignment use.

The analogous merged lower-pair families71,80,589,590 introduce a central
square containing both lower inner markers. The existing forced-point
theorems can yield directional alternatives once their actual auxiliary
owners are established, but no complete terminal for all alternatives was
derived in this review. These are separate mathematical obligations, not
missing literals in the current four-square interface.
