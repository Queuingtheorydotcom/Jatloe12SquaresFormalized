# Complete C898 relaxation and vertical-transition source

The original square model, continuous angle coverage, strictness bits, exact
enclosure rows and original domain transitions are preserved. This document
records source assembly and exact arithmetic audits; it is not a Lean replay
receipt or a claim that C898 or the global theorem has been accepted.

## Relaxations

All 2,048 original relaxation links contain 26,174 target-row occurrences.
Exactly 2,048 occurrences are source-row aliases. The other 24,126 occurrences
use two source rows and a nonnegative constant slack; 15,504 distinct numerical
checks suffice after exact sharing. Every old rational certificate was checked
for nonnegative weights, zero affine sum and genuine strictness before the
new two-row representation was accepted by the audit. There were no fallbacks.

The old links contain 4,424,239 bytes of rational weight text. The complete new
relaxation modules contain 763,902 bytes and 20,307 Lean lines, including the
shared support records, all links, membership checks and named original-link
aliases. This comparison does not include the common pose dictionary in either
side. It is not a measured compilation-time reduction.

`Compact.Core.RowSupport` reconstructs integer Cramer weights and lets the
existing sparse checker verify all signs, affine identities and strictness.
`Compact.Bridge.IndexedRelaxation` proves the resulting implication for the
original `PoseLeaf.OrientedRealizes` predicate. In particular, both the actual
orientation witness and inner-reference containment are retained.

Entry point: `Compact.Cases.C898.Relaxation.All`.
Original names and indices: `evidence/c898-relaxation-link-map.json`.
Audit: `audit/c898-relaxation-supports.json`.

## The two vertical transitions

All 105 historical plans are replaced by the complement of one closed
coordinate interval. There are 210 exhaustive alternatives: 43 are excluded by
two-row support bounds, and 167 transfer into original surviving pieces.
Several alternatives share the same unchanged piece. No region-tree expansion
or old empty-node certificate is used by this replacement.

The three neighbor domains of each transition share one common vertical-cut
window. All 312 neighbor leaves cover that window after 624 planar two-row
checks. This replaces their historical four-dimensional pair certificates.
For each neighbor, the checked inequalities are

```
upperWindow - radius ≤ centerX ≤ lowerWindow + radius.
```

They imply a long vertical section for every cut in the common window. The
source radius chooses one such cut whenever its center is in the excluded
interval. The compact long-section theorem and four-square capacity theorem
then supply the contradiction, for every actual angle in its closed interval.

The radius values are the original 64 rational certificates. Their quadratic
conditions have new ordinary Lean proof terms; the historical native radius
checks are not used. The data and complete step assembly occupy 1,149 Lean
lines and 52,107 bytes, excluding generic shared geometry and row support.

Entry points: `Compact.Cases.C898.ChordStep9` and `ChordStep10`.
Audit: `audit/c898-chord-supports.json`.

## Exact initial binding

`Compact.Cases.C898.Initial.SharedAll` states the equality between every initial
owner's leaf list and the shared pose dictionary. All 1,121 leaves retain their
exact input-row order and angle. Its public `ownerN_oriented_cover_shared`
theorems supply the initial inputs for the new transition chain.

## What backward slicing can and cannot remove

An exact domain-level backward slice from the terminal empty domain retains
all 15 transitions and all 11 initial owners. Omitting any complete angle
interval is not justified by that slice; even an initially empty angle root
still needs its exclusion proof. See `audit/c898-backward-domain-slice.json`.

The remaining direct initial-data reduction is representational: contexts are
computable from root rows and cut edges. The separate traversal checker can
remove 41,616 stored context records while preserving every branch. Current
initial data is frozen pending validation. Combining initial and shared pose
row dictionaries can also remove 15,243 duplicate row records; identifying a
row with its strict complement further reduces the combined 40,307 exact rows
to 30,602 signed classes. Those two dictionary reductions are measured possible
savings, not yet applied source savings.

No bound for the other six previously accepted cases or the unfinished global
case split follows from this one-case conversion. Global source-size and
compilation-time claims require their complete dependency and certificate
accounting.
