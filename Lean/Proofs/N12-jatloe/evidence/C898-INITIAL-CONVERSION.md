# Complete C898 initial-enclosure conversion

The full source is assembled at `Compact/Cases/C898/Initial/All.lean`.
It covers all **704 initial angle roots**, grouped into all **11 original
owner enclosures**, and preserves all **1,121 surviving leaves** in the exact
original owner/angle/leaf order. The subsequent 15 propagation steps are
separate work. Generated theorem statements are not yet acceptance receipts;
the root worker owns Lean validation.

## Checked representation and original geometry

`Compact/Core/RegionDAG.lean` proves direct graph soundness. Each context is a
single `(parent, row, depth)` record. A cut must have both earlier children,
the exact strict complement, and the correct context extension on each side.
No graph is expanded into a `RegionTree` value. Empty nodes use the ordinary
integer sparse-certificate checker. Forbidden nodes must cite an actual
forbidden block and prove that all its rows occur in their context.

The original 3,522 forbidden nodes use blocks already present as positive
ancestor tests. Membership therefore replaces **14,088 tautological Farkas
implication checks**. All 10,149 genuine empty certificates remain, with
36,103 weighted row terms. Cut equality boundaries retain the original
strict-complement semantics.

`Compact/Bridge/RegionOwner.lean` binds each root to the unchanged
`S12.poseInputs` and `S12.poseForbidden` formulas and proves the full original
`S12.OrientedPoseCovered` conclusion. It preserves the actual `OpenSquare`,
side bounds `1 < side ≤ 1001/1000`, containment, original required/excluded
points, continuous angle coverage, inner reference containment, and the
square's actual angle witness. The 64-angle coverage proof uses ordinary
kernel reasoning rather than the historical native-decision coverage lemma.

## Full initial-source cost

| Measure | Converted source |
|---|---:|
| Lean bytes | 5,882,607 |
| Lean lines | 124,996 |
| Lean modules | 62 |
| Shared integer rows | 29,524 |
| Persistent context records | 41,616 |
| Direct graph nodes | 28,880 |
| Surviving leaves | 1,121 |

Numerical rows are shared across all 11 owners at each angle. This removes
15,060 row copies compared with isolated per-root dictionaries while keeping
each dictionary bounded. Positive denominators are checked once per angle.
Leaves are context aliases, so their full row lists are not copied into the
source. Sixteen roots share each data module.

The authenticated historical 704 root declarations occupy 6,615,334 bytes,
plus 81,252 bytes for their check declarations, before owner assemblies and
angle infrastructure. The new total above includes owner assemblies and
angle coverage. The substantive change is fewer arithmetic obligations and
direct integer/graph replay; physical line count alone is not a timing result.

## Provenance and validation boundary

`scripts/convert_c898_initial.py` encodes the authenticated
`evidence/C898/raw/data/region898.json`. It checks exact integer zero-sum
identities, nonnegative weights, positive-weight strict sources, source-row
membership, forbidden-block membership, every context extension, original
leaf row order, original global owner leaf order, and exact rational geometry
formulas. It writes data and Lean statements, never unchecked theorem results.

The complete last encoding pass took 2.08 seconds and 126,599,168 bytes peak
RSS on macOS. It launched no child processes, proof searches, solvers,
compilers or network calls. Full per-root counts, original leaf indices,
source hash and exact output sizes are in `evidence/c898-initial-conversion.json`.

Lean compilation receipts belong in `.verification/`. Until those pass,
this is a complete source assembly with exact encoder validation, not a
kernel-validated initial enclosure or a finished C898 exclusion.
