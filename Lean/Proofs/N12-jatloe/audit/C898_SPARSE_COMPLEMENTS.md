# Proposed sparse complement dictionary

The proposal is staged at `evidence/proposals/PairComplements.lean`; the active pilot file is unchanged. `scripts/prepare_c898_sparse_complements.py` reproduces the proposal and its audit without running Lean or any historical generator.

## Exact lookup coverage

All 601 plans in the thirteen active `PairStep00`–`PairStep14` modules, excluding chord steps 09 and 10, were read from their actual Lean source. The 500 nontrivial block IDs occur exactly once across these plans. Their block-row lists were read independently from `PairRecords.lean` and agree exactly with the authenticated conversion catalogue. Their union contains 725 row IDs.

The entire active Compact source was searched for `complement`, `C898Shared.complement` and `complementData`. The C898 dictionary has only these consumers:

- Each of the thirteen step modules passes it to `PairPlan.Check` and `pair_step_sound`.
- `PairPlan.contexts` passes it to `outsidePieces`, which applies it only to rows of that plan's selected block.
- `PairPlan.Check` also applies it only to rows of that same block, requiring exact equality with `RegionDAG.opposite`.
- `PairPlan.sound` passes the checked equalities into `outsidePieces_sound`.

Other search matches in RegionDAG and RegionTraversal are independent locally bound row IDs; ChordPlans mentions interval complementation only in prose. `PairRecord.Check` does not use the complement dictionary at all.

`evidence/c898-sparse-complement-proposal.json` lists every step, its exact block IDs, and every used row ID, together with hashes of the audited sources. All 725 used values exactly match the old 26,026-entry table. Independently, every returned integer row is the negation of the original three coefficients with its strictness flag flipped; denominators also agree. This is source/data evidence, not Lean acceptance.

## Total lookup and arbitrary inputs

The proposal stores sorted `(key, value)` pairs and searches them with a structurally recursive, fuel-bounded binary search. It has no partial or unsafe definition. At most ten search steps are needed for the current table. A missing key returns row zero, as did the previous table's fallback. The 2,313 previously nonzero entries outside the used set become zero.

These arbitrary defaults cannot weaken the generic theorem. `PairPlan.sound` accepts an arbitrary complement function and requires `PairPlan.Check`. For every selected block row, that check verifies the actual returned row equals the exact strict complement. If a future plan uses a missing key and zero is the wrong row, its check fails; if zero is genuinely the required opposite, using it is sound. A no-block plan never looks up a complement, and an empty block has no lookup. Context coverage is checked separately using that same function.

The other fallback, `pairRecordAt` on an out-of-range array index, remains guarded independently: a plan check requires its witness index be less than the record count, and the soundness theorem requires every record within that bound to pass its actual geometric check. Sparse complement lookup changes neither requirement.

No change to the original exclusion, its assumptions, or any generic soundness theorem is proposed. Activation and Lean replay remain pending.
