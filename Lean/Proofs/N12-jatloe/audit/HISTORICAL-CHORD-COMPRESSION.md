# Twenty original chord transitions

The remaining six-case routes contain 21 chord stages. C713 step 5 has its
separate occupied-row height replacement. The other 20 can discard their
historical subdivision trees and intermediate relaxation poses.

For each original stage, the three original neighbor domains cover a common
horizontal or vertical cut window. The four-square section-capacity lemma
forces the source center outside that window enlarged by its certified angle
radius. This gives two exhaustive **strict** branches. Every whole branch is
checked against an original outgoing pose or an explicit weighted contradiction.
There is no vertex-only claim that a union of target hulls covers an input region.

## Exact audit, not Lean acceptance

The parent ran `scripts/prepare_historical_chords.py --run` successfully in
1.619 seconds. Its complete numerical reconstruction is in
`evidence/proposals/HistoricalChords/certificates.json`; the manifest records
the authenticated original graphs, domains, and source windows.

| Obligation | Count |
|---|---:|
| Original stages | 20 |
| Original source pose occurrences | 1,298 |
| Complete strict interval-complement branches | 2,596 |
| Empty branches | 1,470 |
| Weighted terms in empty certificates | 2,940 |
| Branches implying original outgoing poses | 1,126 |
| Original target row checks | 13,562 |
| Original neighbor pose occurrences | 2,963 |
| Neighbor coordinate bounds | 5,926 |
| Unreconstructed obligations | 0 |

The complete source and neighbor lists are unchanged. Surviving branches imply
every constraint of their original target. Empty branches retain all strictness
bits and are checked by `EmptyContext.Witness.Check`. The producer imports the
same exact local reconstruction helpers used by the direct-pruning audit;
neither Python discovery nor a successful source manifest is a Lean proof.

## Generic checked mathematics

The parent replayed:

- `Compact.Bridge.AxisSection`: 1.418 seconds, ordinary axioms. It handles both
  coordinate directions with the original oriented-pose witness.
- `Compact.Bridge.IndexedChord`: 8.090 seconds, ordinary axioms. It checks the
  complete neighbor cover and both strict source branches against an arbitrary
  original-pose dictionary.

The first source proposal had 53,669 Lean lines and 2,981,016 bytes. That proposal
is preserved, but it is not the intended delivery representation. Most lines
repeated the same data-cache and proof declaration scaffolding.

`Compact.Bridge.ChordSyntax` supplies record commands which elaborate separate
cached data and ordinary kernel proofs. Each original neighbor is one record;
each source is one record containing its two branch outcomes. A generic list
lemma composes the opaque checks. Cached target rows are bound to the original
dictionary by exact equalities. Source records contain original pose IDs,
the radius reference and local witness positions; no duplicated global row
pool or intermediate pose dictionary is introduced.

`Compact.Bridge.ChordPacking.transfer` binds four distinct original owner masks
to a `NormalizedPacking`, deriving their side, container and disjointness facts
from the original packing. The compact stage emitter provides `packing_sound`
with the exact original graph premises, so these results can fill the actual
stage fields without an extra four-square certificate assumption.

The parent ran the no-search rerender
`scripts/compact_historical_chords.py --run` successfully in 0.28 seconds.
Its exact output is 21 modules, 7,692 Lean lines and 924,978 bytes in
`evidence/proposals/HistoricalChordsCompact`: a reduction of 45,977 lines
from the first representation, with all original obligations retained.
The larger original proposal is preserved.

Only the shared radius table and two complete stage pilots, C717 step 18
(vertical) and C701 step 23 (horizontal), have been activated for Lean replay.
Their exact copied hashes are in
`evidence/historical-chord-pilots-activation.json`; all other stages remain
in the isolated proposal. Activation changes no mathematical validation status.

## Remaining validation boundary

The command helper, packing adapter and all 20 concrete stage certificates still
need fresh Lean replay at this checkpoint. Neither whole C898 completion nor
any of the other six whole-case exclusions follows from the audit alone.
The compact proposal's exact size is recorded in its generated manifest;
there is no extrapolated global line-cap claim here.
