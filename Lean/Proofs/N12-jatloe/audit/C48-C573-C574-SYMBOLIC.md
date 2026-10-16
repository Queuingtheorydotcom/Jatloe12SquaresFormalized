# Cases48,573,574: genuine shared entrance, continuous ending still open

The new source `Compact/Bridge/C48RightBarOwnership.lean` constructs
`CertifiedDomain` lists from the original normalized packing and the
checked single/combined ownership specifications. It proves the same18
common point-membership statements for each family. Its ordinary finite
checks have not yet been replayed in Lean.

The real cardinality budgets are F3/G2. Ordinary selected squares may own
one or two F points; the merged right central owner1536 may own zero or
one. All selected G sets are singletons. The two paired corner owners48
and192 remain actual squares, although their auxiliary domains need not
be enumerated for this entrance.

Case48 uses the bottom corner owner4;573 replaces it by8192;574 replaces
it by8196. For8196 the F-domain retains one or two points and the genuine
wall-pair seed segment supplies F6=(2.4,1). The same segment supplies
G5=(2.26,1). Using `singleSpec70` unchanged would incorrectly restrict
this F-domain to cardinality one; the new source deliberately avoids it.

The parent-run exact diagnostic `evidence/right-bar-broad-domains.json`
finds8,8,10 feasible auxiliary assignments respectively, using39,41,49
DFS nodes. This is a finite diagnostic, not a Lean acceptance receipt.
It preserves the extra F choices and confirms these common geometric
inputs:

| Actual owner | Common additional points |
|---|---|
| SW256 | (2,1.74),(1.74,2) |
| NW2048 | (1.74,3) |
| right pair1536 | (2.26,2) |
| top32768 | (2.4,3),(2.26,3) |
| left wall4096 | (1,2.26),(1,2.4) |
| right wall16384 | (3,2.26),(3,2.4) |
| bottom4/8192/8196 | (2.4,1),(2.26,1) |

The original markers, container, common side and pairwise disjointness
remain available. None of these three whole cases is excluded by the new
entrance alone.

## Exact boundaries on theorem reuse

Reflecting the completed C84 two-square geometry sends its merged left
pair to1536, but sends its other square to a southwest square that must
also own the bottom marker(2,.914). Owner256 does not own that marker.
This missing premise drives C84's slope bound, so it cannot be discarded.

The existing four-square template also cannot take its A square to be
1536: its `aG` field requires the southeast marker to be absent, whereas
1536 owns both southeast and northeast markers. An earlier informal
reuse suggestion was withdrawn; no Lean source uses it.

If NW2048 additionally owns F5=(2,2.26), horizontal reflection produces
an outer-top elbow with points(2,2.26),(2.26,3),(2.35,2.35), an ordinary
right wall, a top square owning(1.6,3),(1.74,3), and an actual paired
northeast corner. This matches the still-unfinished continuous geometry
being studied for C981 rows34/41. It is not an already-proved ending.

The right pair1536 cannot own F3=(1.6,3): its southeast marker is farther
from F3 than the normalized square diameter. The two extra574 choices
placing F3 or F5 on8196 are likewise excluded by its genuine bottom or
southeast-bottom marker. These are ordinary diameter consequences; they
have not been used to assume away an unproved continuous ownership case.

## Remaining whole obligation

A successful shared ending must retain the actual southwest square,
right pair, right wall and relevant singleton/corner neighbors. Positive
points of just the southwest/right-pair squares admit separating
placements. Conversely a right-pair/right-wall relaxation admits a
negative-angle escape. These observations identify missing interactions;
they are not countermodels of any original twelve-square family.

No center point, long section or separating-axis selector is currently
assumed for the right pair. A prospective wall-support calculation under
a missing-center assumption would establish a center lemma at most,
not a whole exclusion. The original square interactions still have to
close that remaining center/angle cycle.
