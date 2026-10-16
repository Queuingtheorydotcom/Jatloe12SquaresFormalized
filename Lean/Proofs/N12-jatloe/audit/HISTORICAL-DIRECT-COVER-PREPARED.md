# Direct initial covers for the other six historical cases

Prepared on 2026-10-11. **The audit has not been executed.** No new numerical
success, complete case exclusion, or global size saving is claimed here.

The parent has accepted `Compact.Core.PlanarVertex.nonnegative_of_vertices`
(9.088 seconds) and separately audited all 704 C898 initial roots by exact
boundary intersections, including all 74 empty angles. That finite C898 result
motivates replacing the initial forests and incoming relaxations with a direct
cover. Each integer checker instance and original-case adapter still needs Lean
acceptance. The six other historical cases must be audited independently.

## Prepared artifact and resource boundary

`scripts/audit_historical_direct_cover.py` is prepared for cases
701, 713, 717, 973, 978 and 979. It performs no Lean generation or compilation,
archive extraction, recovered-program execution, network access, or proof-source
mutation. The only eventual output is a bounded JSON evidence report.

It requires explicit `--run`, enforces an internal 115-second working limit
within a 120-second external slot, 256 MiB process RSS, and an 8 MiB output cap.
Gzip Lean sources are read a bounded line at a time. Historical JSON trees are
skipped in 64 KiB buffers, retaining only owner, angle-count, inside and outside
metadata; their full raw bytes are still hashed. Failed mappings and incomplete
owners are recorded as unsupported. Timeouts save a partial report and do not
imply missing roots are empty. Temporary output is removed on failure.

Parent-only suggested first pilot:

```sh
python3 scripts/bounded.py --rss-mib 256 --seconds 120 \
  --receipt .verification/historical-direct-cover-713-resources.json -- \
  python3 scripts/audit_historical_direct_cover.py --run --case 713 \
    --output evidence/historical-direct-cover-713.json
```

Omitting `--case` requests all six within the same cap; repeated `--case`
arguments select a subset. The source has passed a static Python syntax parse.
Neither its mapping nor its geometry loops have been run by this worker.

## Differences found by source inspection

The six routes do not use a universal 64-bin / eleven-owner entrance:

| Case | Grid in the first original root | Owner slots used by the original final mixed theorem |
|---|---:|---|
| 701 | 64 | 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 |
| 713 | 128 | 0, 1, 5, 6, 7, 8, 9, 10, 11 |
| 717 | 128 | 0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11 |
| 973 | 64 | 0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11 |
| 978 | 64 | 0, 1, 5, 6, 7, 8, 9, 10, 11 |
| 979 | 128 | 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 |

These are inspected first-root and final-wrapper facts, not results of an
all-root audit. The prepared audit derives every owner's actual grid, mask and
literal target list independently. It reports all initial owner domains rather
than silently dropping owners unused by the final theorem. Restricting a later
translation to the needed owner closure requires a separate dependency check.

The inspected original wrappers are in `Push701Chunk56`, `Push713Chunk92`,
`Push717Chunk160`, `Push973Chunk74`, `Push978Chunk73` and `Push979Chunk160`.
They invoke `common_certified_enclosure_sound`, followed by the original
oriented incoming relaxation, before the mixed theorem. The shared
`PoseRegion` and `OwnerEnclosure` interfaces use `1 < q.side ≤ 1001/1000`
and containment in the side-four container. The audit requires their exact
source hashes to match the C898 generic semantics, in addition to recognizing
these bounds. Different helpers are explicitly unsupported.

## Exact mapping and checks performed when run

1. Read each historical `case-replay.json` source-hash map. Authenticate every
   consumed `Push{case}ChunkN` module against that receipt, reading the recovered
   gzip source directly. Record module paths, exact original hashes and bytes.
2. Match original `region{case}Inside{owner}` / `Outside{owner}` literal lists
   against the authenticated `data/region{case}.json` metadata, preserving point
   order and every exact rational coordinate. Record the owner-to-marker-mask
   mapping from the actual original packing wrapper.
3. Read each literal `owner{case}_{owner}` root list. Require the original
   root-check declarations to use exactly that owner's inside/outside premises.
   Derive the grid from each root's angle declaration, and check complete
   ordered coverage of every closed bin from 0 to 1. Parse the full seven
   rational angle-enclosure fields from the authenticated original `AngleData`.
4. Read literal `continuousScout{case}Domain{owner}_0` lists and their
   `continuousScout{case}Initial{owner}_{index}` declarations. The angle stored
   inside the `PoseLeaf` determines the key; its suffix index is never treated
   as an angle. Require at most one target per owner-angle. Preserve every
   non-strict row; discard only a strictly positive constant tautology.
5. Construct the original compulsory-point outer relaxation at side bound
   `1001/1000`, the four wall bounds, and open inner-reference rectangles for
   the forbidden points. Replace parallel compulsory bounds by their exact
   strongest positive-scale form. Never reverse a row's sign or turn an open
   forbidden rectangle into a closed one.
6. Enumerate all nonparallel boundary-line intersections with exact rational
   arithmetic. Retain intersections satisfying every closed compulsory/wall
   bound and lying outside each open forbidden rectangle. Check every surviving
   vertex against every target row. If the literal domain has no target for an
   angle, require that the complete closed feasible vertex set is empty.
7. Report every checked root, target name, boundary-pair count, surviving vertex
   count and failure. A missing owner domain, repeated target angle, nontrivial
   strict target, mismatched grid, alias or unsupported source shape produces
   an unsupported result, never an inferred empty domain or cover.

The original wrapper's statement is retained in the report for review. This
finite check does not reprove the actual packing-to-compulsory-point entrance,
angle-enclosure soundness, orientation witness, integer checker instances or
replacement Lean adapter. Those must connect the accepted planar theorem to
the unchanged original case contract. Even universal success for these six
initial covers would leave all subsequent pair/chord transitions and final
case assembly to preserve and measure.
