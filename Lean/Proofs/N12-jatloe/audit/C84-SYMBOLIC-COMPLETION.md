# Case84: original-family symbolic completion

Status: the whole original-family Lean source is assembled and independently
hand-reviewed. **The new source and its finite ownership checks have not yet
been compiled.** This is not a completed Lean replay or a claim about the
global twelve-square theorem.

The public entrance is `N12Compact.C84Complete.family_impossible`, in
`Compact/Bridge/C84Complete.lean`. Its only hypotheses are an original
`NormalizedPacking` and equality of its marker family with
`{1,2,4,8,48,192,1024,2304,4096,8704,16384,32768}`.

## Genuine ownership entrance

This family has three F-exempt owners and two G-exempt owners. Ordinary owners
may therefore have two F points; the merged left pair may have one. An
F-cardinality-one specialization would incorrectly discard original packings.

`C84Ownership` preserves these budgets. It combines the existing checked
broader specifications for the eight ordinary owners with the actual budget
domains for the two merged owners. Reflection transports the complete owned
sets, including optional points. The two paired corner domains are omitted
from the finite cover, which only enlarges that cover; all twelve squares
remain in the original packing.

The historical G-domain for owner8704 was not restored as a theorem. It is
replaced here by original geometry. `C84MergedBottom.forbidden` proves three
continuous exclusions, and four other exclusions follow from the diameter
bound. The exact singleton G-budget then gives the new authenticated domain
`[{5},{6},{8}]` in `C84MergedBottomDomain`. No archived domain array is assumed
to be geometrically sound.

The parent's exact finite diagnostic found thirteen complete assignments in
61 search nodes; see `evidence/c84-broad-domain-audit.json`. Every assignment
forces the needed G points. This diagnostic is **not** the Lean proof. The
source separately states ordinary kernel finite checks through
`ForcedAuxiliary.withoutPoint`; those checks and their original-packing
soundness bridge still await the deferred compilation. Inherited checked
specifications retain their existing native-certificate trust model.

## Complete continuous ending

Only the two actual merged squares are needed at the final contradiction:

- B, owner8704: the bottom marker `(2,.914)`, the SE central marker
  `(2.35,1.65)`, and the forced point `(2.26,2)`.
- W, owner2304: both left central markers and the forced point `(1.74,2)`.

Actual owner4 supplies `(2.26,1)` and `(2.4,1)`, so both are absent from B.
Disjointness also makes the SW marker absent from B.

After choosing a canonical face frame, the missing corner auxiliary rules
out a nonpositive B angle. The missing G5 point forces
`B.loV >= c - 2.26*s`. The strict bottom marker consequently gives `s > .3`.
The missing SW marker then forces `B.loU >= 1.65*(c+s)`.

`C84MergedPair` eliminates all eight directions on the four separating axes
of B and W. Its only scalar splits are continuous relative-angle and support
endpoint comparisons; there is no angle-bin table or pose enclosure. The
negative-W longitudinal comparison uses the two actual W anchors, with the
switch at their projection equality `35*(-W.s)=9*W.c`. The transverse
comparison uses the B-angle and diagonal endpoints of a linear cone.

`C84PairMargins` supplies the short unit-circle inequalities. The complete
ending retains side greater than one, genuine strict points, arbitrary
physical orientations, and actual disjointness. It assumes no auxiliary
center point or extra packing restriction.

## Source footprint and remaining boundary

The replacement consists of six small Lean modules: the scalar margins,
merged-bottom geometry, original G-domain, broad ownership entrance, complete
two-square contradiction, and original-family bridge. It introduces no
generated angle cases or certificate trace. The exact project-wide line
census is maintained separately by the parent; this note does not substitute
a guessed total for that census.

The whole C84 mathematical obligation is now source-complete and independently
hand-reviewed. Final acceptance still requires the deferred Lean checks and
the original retained-row registry binding. Cases48/573/574 remain separate
obligations: their merged central owner does not supply B's bottom marker, so
this ending cannot simply be reused by dropping that premise.
