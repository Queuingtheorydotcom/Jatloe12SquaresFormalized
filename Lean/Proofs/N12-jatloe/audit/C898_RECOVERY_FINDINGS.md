# C898 source recovery and compact conversion

The first bounded recovery completed in 440.3 seconds, with 318,464 KiB peak
aggregate resident memory. It downloaded 4,040,163,328 bytes sequentially,
retained 18,629,455 bytes including the archive line-count table, and left
no processes running. Compressed parts were SHA-checked before decoding;
every retained source/data file was checked against the pinned historical
source manifest. The entire archive stream was not traversed or certified.
No recovered program was executed and no Lean compilation was performed.

The complete machine receipts are `c898-record-restoration.json` here and
`../.verification/c898-source-recovery-resources.json`. The requested raw
records are under `../evidence/C898/raw/data`.

## Current recovery boundary

A second bounded stream recovered **all195 original C898 Lean modules**,188,138,692 bytes, authenticated against the pinned source manifest. Its broader numerical-file recovery stopped on a macOS temporary-filename length error after814 new files/203,025,761 bytes had been retained and authenticated. The decoder exited and was cleaned up. The filename implementation was corrected; no third full stream was started.

Consequently C898's actual accepted source, including all15 later transitions and final assembly, is now available. The separately missing numerical records are **not** a missing C898 witness: its original Lean contains every witness needed for this conversion. The other-case numerical corpus remains incomplete. See `C898_COMPLETE_RECOVERY_MANIFEST.json`, `c898-recovery-interruption.json`, and `C898_REMAINING_RECOVERY_MANIFEST.json`.

## Exact conversion now performed

- Entire initial cover:704 roots/11 owners, translated to124,996 lines/5,882,607 bytes with shared per-angle rows and persistent contexts. Shared `RegionDAG` soundness passed Lean; full generated data remains to be checked.
- All13 pairwise transitions:25,843 overlap certificates and206,744 strict inequalities reconstructed from four row indices, with zero fallbacks. Original96,595,850-byte rational-weight text becomes1,653,952 bytes of support indices before metadata. `PairSupport` soundness passed Lean.
- All2,048 relaxation links:2,048 aliases and24,126 two-index support occurrences,15,504 distinct checks; zero fallbacks. This removes4,424,239 bytes of old rational-weight text. Data and bridge replay remains pending.
- Pair cut coverage:all601 plans are101 unchanged leaves,63 complete exclusions or437 single forbidden blocks. One prefix-complement argument replaces725 explicit tree cuts and preserves all826 surviving pieces.
- Two chord transitions:all105 plans reduce to interval complements,43 small support exclusions and167 branch transfers. Their312 neighbor leaves require624 two-row window checks. Generic geometric integration is underway.

Producer-side exact audits are not Lean acceptance. The entry enclosure, all transitions, original owner/case identity and final exclusion must still pass together before calling C898 compactly replayed.

## What the recovered initial region record contains

`region898.json` is an exact initial owner-cover certificate, not the final
C898 contradiction. It has 11 owner records, each with 64 orientation roots,
inside/outside point data and a list of resulting leaves. Its 704 trees
contain 14,088 cuts, 10,149 empty nodes, 3,522 forbidden nodes, and 1,121
surviving leaves. All 1,121 leaf alternatives still require subsequent
geometric reasoning.

An affine constraint is `[[a,b,c],strict]`, meaning the linear form
`a*x+b*y+c` has the specified strict/non-strict sign. Rational values are
encoded as strings, with some integral coefficients represented as JSON
numbers. Empty-node terms are `[constraint,weight]` pairs. Empty certificates
have three terms at 4,493 nodes and four terms at 5,656 nodes. A replacement
that handles only two weighted rows cannot check these records.

The tree tags are:

- `cut`: one test and complete `yes`/`no` subtrees;
- `empty`: exact weighted Farkas terms;
- `forbidden`: a forbidden block plus one implication certificate per row;
- `leaf`: an index into that owner's retained leaf list.

The finite data contain 23,432 distinct exact JSON row encodings and 9,911
distinct empty certificates. These are syntactic counts: clearing positive
denominators may identify more repeated rows, but must adjust weights and
preserve strictness.

Every forbidden node's block rows are literally positive tests on its
ancestor path. This was checked by traversing all 704 roots. Its four
implication certificates each have two unit-weight terms. Consequently a
generic rule that checks membership of the forbidden block in the current
assumptions can replace all 14,088 of these tautological implication
certificates. This is a concrete data simplification opportunity, not yet
an accepted whole-case Lean proof. Details are in `c898-initial-schema.json`.

The recovered historical CompactRegionTree decoder builds RegionTree values
from earlier array entries and applies the existing tree checks and leaf
enumeration. It is a text encoding rather than a shared semantic DAG replay.
The new representation should preserve shared states and prove its local
rules once instead of reproducing that expansion.

## Historical limitation of the first recovery (now resolved for C898 source)

The authenticated batch manifest says the accepted assembly continues through
`ContinuousScout898Step0` to `ContinuousScout898Step14`, then
`MixedGeometryScout898`, `Case898Domains`, `Case898RefinedDomains`,
`CommonPoints898` and `SharedCase898`. The last six declarations are included
in `Push898Chunk65`; their original separate files are not all retained in
the historical manifest after batching.

Those first region/input/batch records did not contain the propagation
or terminal certificates. In particular, the batch manifest records source
identities and dependencies, not all their proof witnesses. A reconstruction
must still connect original owner-domain coverage to the initial covers,
connect the incoming cover to the Scout cover, preserve every propagation
alternative, and reach the final contradiction. Initial empty regions alone
are insufficient.

Eight additional named C898 data files are present in the source manifest:

| Path under `data/` | Bytes |
| --- | ---: |
| `caseScout898-input.json` | 100 |
| `chordScout898-proposal.json` | 31,928 |
| `continuousScout898-certificate-index.json` | 33,367 |
| `incoming898ToScout898.json` | 2,834 |
| `regionScout898.json` | 381,651 |
| `step-domain-snapshot-Scout898.json` | 588,252 |
| `scout-898-minimize.log` | 569 |
| `scout-898.log` | 5,029 |
| **Total** | **1,043,730** |

These separate numerical records remain uninspected; the subsequent complete Lean-source recovery supplies their proof witnesses directly. Filenames such as proposal, snapshot and
index do not establish that exact Farkas witnesses survive; generator
inspection may show that weights must be recomputed. The relevant generator
entrypoints include export_continuous, export_mixed_continuous,
export_shared_mixed_case, export_domain_refinement and export_common_points.
All original scripts together occupy only 607,369 bytes.

`C898_NEXT_RECOVERY_PLAN.json` lists exact paths, source hashes and sizes.
Its diagnostic C898 selection includes the eight records, all original
scripts, the small checker interfaces, and the 2,921,647-byte final batch.
It would retain 4,736,717 additional bytes. The second stream described above has since recovered the complete C898 Lean closure; this earlier small-selection plan is retained only as provenance.

## Broader recovery cannot yet be called complete

All data files whose names identify one of the seven accepted case numbers
occupy 131,664,299 bytes in 97 files, of which 120,633,535 bytes remain to
retrieve. Naming is not proof ancestry: some imported helpers or redirected
cases can have other labels. C979 also lacks a matching step-domain snapshot
in this manifest.

A conservative candidate that adds every non-region baseline data file,
all original scripts, the C898 checker interfaces and final batch would
retain 215,947,526 additional bytes. It still omits most baseline initial
region certificates; all archived data occupy 1,345,253,074 bytes, including
1,245,210,563 bytes of region records. Therefore the current evidence does
not justify promising that a small second selection contains every witness
needed for all seven exclusions and the 117-to-18 reduction. Resolve the
specific C898 entry, propagation and terminal chain before generalizing.
