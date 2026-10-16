# Exact original entrances for all six historical cases

Source preparation, 11 October 2026. No whole-case or full entrance acceptance
is claimed here. The parent owns all execution and Lean replay.

| Original case | Actual owner slots | Angle grid | Complete root obligations |
|---|---:|---:|---:|
| 701 | 12 | 64 | 768 |
| 713 | 9 | 128 | 1,152 |
| 717 | 11 | 128 | 1,408 |
| 973 | 11 | 64 | 704 |
| 978 | 9 | 64 | 576 |
| 979 | 12 | 128 | 1,536 |
| Total | 64 | Both original grids | 6,144 |

The root inventory, inside/outside points and original owner masks come from
`evidence/historical-direct-cover-audit.json`. Its exact finite audit passed;
that receipt does not replace Lean checks. The five new cases account for
4,992 roots; C713's separately owned proposal accounts for 1,152.

## Prepared source and exact contract

`scripts/prepare_historical_initial.py --run` prepares only
`evidence/proposals/HistoricalInitial`. It leaves active source and the C713
producer alone. The parent must run it serially within its256MiB/115second
guard. The source-output ceiling is12MiB, with no numerical searches,
subprocesses, compiler invocation or network access.

The producer retains:

- Every original angle, including empty roots, and exact selected original
  premise indices. No original coefficient table is duplicated.
- Every original reduced pose ID and its order in the initial domain.
- The one existing192-angle/global-pose bank shared with C713.
- The existing `Preservation.C*.lean` domain tables, with no second serialized
  copy of their IDs.
- All original local-query, owner-domain refinement and convex owned-point
  proofs needed by the actual packing entrance.

The generated theorem `N12Compact.C701Entry.owner0_cover`, for example,
takes only an original `NormalizedPacking p` and
`codedMarkerFamily p = Preservation.C701.family`. It concludes the original
`OrientedPoseCovered Preservation.C701.continuousScout701Domain0_0`
statement for the actual owner. The same pattern supplies the exact
`Pending.initial{owner}` fields of the existing six semantic graphs.
No pose coverage, point ownership or geometric exclusion is assumed of p.

Each root is one `checked_recipe` source record. That accepted command emits
a named cache and separate ordinary kernel-checked numerical theorem. Eight
records share a module; the five-case producer has624 numerical modules.
No target-row pool, boundary-hint table, subdivision tree or raw incoming pose
is regenerated. The all-six root count would require768 such modules.

## Original ownership boundary

The six authenticated entrance intervals are in the final source chunks:

| Case | Exact original source | Selected entrance lines |
|---|---|---:|
| 701 | `S12.Push701Chunk56` | 1,613 |
| 713 | `S12.Push713Chunk92` | 1,571 |
| 717 | `S12.Push717Chunk160` | 3,736 |
| 973 | `S12.Push973Chunk74` | 3,169 |
| 978 | `S12.Push978Chunk73` | 3,135 |
| 979 | `S12.Push979Chunk160` | 5,683 |

These18,907 lines are provenance measurements, not the size of the new Lean
closure. The producer checks the uncompressed original-source hash before
extracting anything. Identical local queries reuse their existing canonical
proofs. All newly emitted checks use ordinary kernel decisions.

There is a real case distinction in the owner certificates: C717 and C979
contain upper bounds of three. The accepted `SmallOwnerDomain` shortcut
requires an upper bound of two and cannot justify those declarations.
The new `Compact.Bridge.SmallOwnerDomainThree` instead proves completeness
of the176 subsets of size at most three, using `Finset.card_eq_three` and
six possible orders of three distinct elements. It checks cached query
signatures, then proves the same original `DirectSingleDomain.Check`.
The producer lists every upper-three declaration and selects this separate
theorem; the smaller existing checker remains used for bounds at most two.
The new generic theorem and its concrete instances await parent replay.

## Remaining checks and source budget

The producer has not been run by this worker. Its manifest will report exact
module/line/byte counts and the five new cases' record provenance before
activation; C713 has its separate manifest.
The counted roots do not include the pending pair/chord propagation proofs.
Neither a full preservation bound of300,000 lines nor a complete final proof
under one million lines follows from these entrance counts alone.

Required acceptance remains: every numeric root, full continuous angle cover,
exact original reduced-domain equality, original ownership certificates,
and the unconditional packing-to-cover entry theorem. Only then may each
graph's initial obligation be marked complete. Whole-case completion also
requires every active transition and the terminal contradiction.
