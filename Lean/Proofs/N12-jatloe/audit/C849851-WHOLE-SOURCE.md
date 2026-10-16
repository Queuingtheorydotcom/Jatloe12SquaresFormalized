# Original 849 and 851: complete source argument

11 October 2026. Both whole original case exclusions are assembled in
`Compact.Assembly.C849851`. This is source completion, not Lean acceptance.
No compiler has been run for these additions. The final full replay remains
required, including the finite ownership checks and original-row bindings.

The original rows are 436 (case 849) and 438 (case 851). Their only family
difference is the right owner's mask, 16384 versus 16416. The true original
auxiliary budget and existing certified domains force the same ten-owner
assignment. The merged top owner retains both its original markers.

## Mathematical simplification

The central/right pair forces A to contain (2,2.5), uniformly in orientation.
This entrance uses the right square's actual marker (3.086,2), owned
auxiliary (3,2.4), and excluded auxiliary (3,1.74), together with its
full disjointness from A. `FourSquareLowerBarrier.right_point` first
forces the right square to contain (3,2.5), and `FourSquareANarrow`
then gives the required point of A.
A canonical face reindexing of the actual top square B leaves two signed
sectors; the physical square and every owned point are unchanged.

For positive B, the actual central/right geometry excludes both possible
transverse separating directions. The argument uses the genuine upper-right
owner and upper-left corner owner, with exact continuous scalar margins.

For negative B, the actual upper-left corner square forces the inward
corner point (a,4-a), where a is the common side. This gives the stronger
lower face bound needed at the endpoint. B uniformly owns (1.4,2.6).
The genuine left square L must place its missing lower point below its V
face; otherwise it would also contain that strict point of B.

Full-square separation therefore leaves exactly two directed support
inequalities. The B-transverse possibility is contradicted by L's left-wall
containment and the two genuine upper-right-owner face alternatives.
The L-longitudinal possibility is contradicted for both signs of L's frame.
No angle grid, saved pose assumption or point-only replacement of the wall
squares is used.

The positive-L algebra uses two rational half-angle variables and three
explicit nonnegative polynomial identities. Their 83 positive coefficients
are displayed in `C849NegativePositiveMargins.lean`; exact rational
expansion of the actual source expressions independently verified all three
identities. This diagnostic is recorded in
`evidence/c849-negative-positive-margin-identities.json`. Lean will check
the identities with `ring` and coefficient signs with ordinary proof terms.
These are Bernstein-basis certificates, not calls to an SOS solver.

The first proposed scalar bound was false after discarding the actual
upper-right neighbour. That proposal was rejected. The completed argument
retains its two face alternatives. A separately detected expansion error
in the coefficient of t*C*S was corrected before registration, and every
certificate was re-expanded exactly after the correction.

## Original packing entrance and remaining trust boundary

`Compact.Cases.C849851.Complete` derives every premise from the same original
packing. In particular, the missing left-wall point comes from the actual
mask 2 square's seed; the corner owner supplies its two original markers;
the upper-right owner supplies its actual auxiliary point; and complete
physical B/L and B/E disjointness is retained. An independent source review
found no remaining mathematical premise in that entrance.

A later independent source review caught an invalid earlier seed binding:
the point (3.24,1.87) belongs to singleton mask 8, whereas these families
have merged mask 12. That attempted binding has been removed. The repaired
entrance above uses only actual right-wall ownership and full-square
separation, and the positive ending now uses the shared
`MergedTopFurther.Geometry.positive_impossible` lemma. The reviewer checked
the repaired original-point bindings and disjointness direction; no remaining
premise mismatch was found. This is still a source review, not a Lean replay.

The two actual `ExcludesCase` terms are now in `SymbolicRegistry`. The whole
source assembly now has 75 original-case terms and 42 pending original
case contracts. Earlier scoped replay receipts do not certify these new
terms. The global theorem remains conditional on those pending contracts.
