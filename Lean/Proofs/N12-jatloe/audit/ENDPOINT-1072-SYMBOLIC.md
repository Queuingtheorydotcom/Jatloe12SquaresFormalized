# Exact obstacles after the endpoint reductions

Source-only mathematical checkpoint. This is not a whole-case exclusion or a
counterexample to the packing theorem. The original case entrance remains the
finite ownership calculation recorded by the parent in
`evidence/baseline-endpoint-domain-scan.json`.

## Cases 697–699: the top owner cannot be replaced by one forced point

Their archived common signature has the merged NW/top owner (mask 34816)
own exactly markers 11 and 15, F3 and G4. The existing upper-row template
requires that owner to miss the top marker, so it cannot be applied unchanged.

The proposed implication that this owner must contain `(2, 5/2)` is false,
even after including all of its exact marker and auxiliary exclusions. Take

- normal `(c,s)=(15/17,8/17)`;
- side `1001/1000`;
- `loU=237/100`, `loV=32/25`.

It strictly contains `(33/20,47/20)`, `(2,1543/500)`, `(8/5,3)` and
`(87/50,3)`. Its only marker bits are 11 and 15, its only F point is F3,
and its only G point is G4. At `(2,5/2)`, the V coordinate is `43/34`,
strictly below `32/25`.
Its bounding box is
`x∈[17302,40325]/17000`, `y∈[38160,61183]/17000`, inside the container.
It misses `(1,3)`, both top-left corner markers, and `(113/50,3)`.
The top-left corner square `[0,1001/1000] × [2999/1000,4]` is disjoint
because its right boundary is below `17302/17000`.
These are direct rational substitutions; no Lean certificate or numerical
search was run for this checkpoint.

Consequently the actual merged-owner proof must retain another coupled
square, such as the lower core/right wall chain. The local B signature and
top-left corner do not force the desired point.

## Case 1072: two original ownership patterns, no endpoint span

The parent's exact original-domain enumeration leaves two vectors. They
have two opposite core elbow triangles; the other two core owners own
wall-side pairs instead of the unit-height endpoints needed by
`EndpointRowTemplate`. All existing endpoint/high-right literal matches
therefore fail for a genuine geometric reason.

In the first vector, the NW core B owns `(33/20,47/20)`, `(1,113/50)`,
`(1,12/5)`. The left wall L owns `(457/500,2)`, `(1,87/50)`, `(1,8/5)`.
The top wall's strengthened generic lemma supplies `(36/25,3)`.
Replacing the actual top wall by only that point is insufficient.

An exact disjoint L/B pair has common normal `(4/5,3/5)` and side
`1001/1000`:

- L: `loU=941/1000`, `loV=252/1000`;
- B: `loU=1945/1000`, `loV=557/1000`.

Both fit the container and have the stated exact marker/F/G signatures.
L's maximum U is `1942/1000`, strictly below B's minimum U `1945/1000`.
But `(36/25,3)` has U coordinate `2952/1000`, exceeding B's maximum
`2946/1000`. Thus B does not contain the top wall's uniform forced point.

The remaining opportunity is a coupled separation inequality involving
actual top-wall T, core B and left-wall L, preserving T's orientation and
all three original signatures. No such whole exclusion is claimed here.
The agent stopped isolated point attempts and switched to the shared
849/851 square-separation route at the parent's direction.
