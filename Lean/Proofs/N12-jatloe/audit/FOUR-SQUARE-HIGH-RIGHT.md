# Twenty-one original cases from the higher right point

Status: source-complete; parent-controlled Lean replay is pending. No completion
claim is made from the Python finite audit.

The family is 678, 680, 691, 694, 711, 846, 847, 852, 853, 886, 887, 1073,
and 1074. Its public original-model statement is
`FourSquareHighRightCases.covered_cases_excluded`, in
`Compact/Assembly/FourSquareHighRightCases.lean`.

The separate extra family is 669, 670, 673, 674, 675, 690, 848, and 850,
bound by `FourSquareHighRightExtraCases.covered_cases_excluded` in
`Compact/Assembly/FourSquareHighRightExtraCases.lean`. It reuses exactly the
same geometric bridge. All added HighRight source totals 2,280 Lean lines.

## Shared mathematical argument

The previously checked `FourSquareHighRight.impossible` only needs the right
square to contain `(3, 12/5)` and the strict higher point `(3, 5/2)`.
Its unused premise about `(1543/500, 2)` has been removed. The lower-barrier
variant retains that premise explicitly, preserving its own interface.

For this family the right square strictly owns `(3, 113/50)` and `(3, 72/25)`
after the exact case symmetry. The first is an original auxiliary point; the
second comes from the proved singleton-marker seed theorem. Strict segment
convexity, at parameters `7/31` and `12/31`, gives the two required points.
These are strict query-interior facts, not membership assumptions about an
externally computed closed hull.

## Original ownership coverage

Eight cases (846, 847, 852, 853, 886, 887, 1073, 1074) have the four required
owner sets forced directly by the existing certified domains. Some unrelated
owners remain ambiguous; they do not enter the geometric theorem.

The other five cases have respectively 2, 2, 4, 4, and 4 complete ownership
vectors under those same sound domains. Each case has one template vector.
The eleven alternative branches contain two strictly interior segments with
an exact common point. Seven rational certificates suffice across all eleven
branches. `OwnerSegmentCrossing.impossible` proves their contradiction from
the original packing disjointness; all four segment endpoints are original
markers or auxiliary points.

Coverage uses the original `S12.domain_cases_sound` theorem. The finite
checks retain every assignment, and the Lean proofs extract owner equalities
from the actual whole vector. There is no assumed archived singleton domain,
sampled orientation, or additional separation premise.

Seven of the eight extra cases have unique certified vectors. Case 690 has
two vectors and reuses the same exact crossing as 678. Its two-vector list is
audited exhaustively under its own family and domains. In identifying these
cases, the matcher was corrected to include every marker outside an owner's
exact mask, including globally unused markers. Those missing points follow
from `ExactMarkers`, without a foreign owner assumption.

## Evidence and replay boundary

`evidence/four-square-high-right-family.json` records the direct-domain audit,
including the five cases that it cannot force without geometry. Those five
are completed separately by `evidence/four-square-high-right-alternatives.json`,
which contains every retained ownership vector and every exact crossing.
Both reports retain original input hashes. The audit completes in well below
one second at approximately 21 MiB RSS; it starts no Lean or solver process.

`scripts/build_four_square_high_right_alternatives.py` regenerates all thirteen
adapters and shared crossing literals. The original query memberships,
complete-vector enumeration, crossing identities, and final original-case
row binding are explicit Lean obligations. Only their successful replay can
upgrade this family from source-complete to accepted.

`scripts/build_four_square_high_right.py --extra` regenerates the separate
eight-case family after the thirteen-case writer. Its hashes, exact domain
audit, and all transformed strict endpoint/seed provenance are recorded in
`evidence/four-square-high-right-extra.json`.
