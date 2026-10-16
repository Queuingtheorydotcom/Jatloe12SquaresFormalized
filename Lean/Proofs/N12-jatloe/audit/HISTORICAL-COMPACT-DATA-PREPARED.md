# Prepared six-case compact data assembly

Snapshot: 2026-10-11. `scripts/build_historical_compact_data.py` is source-only
and has not been executed by its author. Parent controls its bounded run.

It streams authenticated source hashes from the six historical acceptance
receipts. A first pass resolves the live Plan-list aliases; a second pass
reads only their pair declarations. Unused predecessor pairs are never stored. It preserves all current Initial/Step pose literals and follows
predecessor pose, domain and Plan-list aliases needed by the actual selected
transitions. C701's first four steps reuse such imported plans; those pruning
obligations must survive removal of the predecessor initial forests.

The emitter verifies each selected source-plan list against its whole source
domain, each actual blocked plan's old witness list against its entire neighbor
domain, and all outgoing relaxation targets against the original target domain.
The actual `PosePruning` block list determines whether a plan has a block. No
absence of parsed witnesses is interpreted as an empty block. Unsupported
multiple-block plans stop the run. Chord region aliases retain explicit source
contracts and are never converted to empty regions.

Outputs are staged atomically in `evidence/historical-compact-data`:

- Shared exact integer rows with positive denominators, pose rows with original
  order and strictness, literal block rows, relaxation endpoints, and contexts.
- All six current domain/plan/transition maps, including reused predecessor
  plans and their complete neighbor domains. Original names map to stable IDs.
- The 192 exact reference values: the original 64-angle grid followed by the
  original 128-angle grid. `unitReference` is exactly `reference 1`.
- Actual Lean row and pose literal modules, with 4,096/2,048 records per module.
  These define usable typed data; they do not assert geometric checks.
- Source-indexed unresolved tree, chord and whole-chain contracts, plus exact
  emitted bytes, lines, modules and source hashes.

The same checked two-row support representation can handle pair inequalities
and outward-relaxation target rows. Its proposed numerical bases still need to
pass the checker. Every strict implication needs either positive slack or an
active strict input. Complete chord contractions, direct initial adapters,
reference identities, Plan coverage and final original-model chain assembly
remain separate obligations. The manifest explicitly says that a full proof
has not been assembled or checked.

Limits are 256 MiB RSS, 120 seconds, 192 MiB scratch and 64 MiB retained output.
The script deletes only its newly created staging directory on failure and
refuses existing output paths. It never compiles Lean or runs recovered code.
The coordinating worker must also use the external resource guard. The source
was parsed as Python, and only small authenticated literal parser examples were
tested locally. No successful full-run or final-size claim is implied.

The first parent run stopped safely at the former 64 MiB SQLite limit
(27.423 seconds, 39,328 KiB peak RSS), with staging removed. The revised
extractor materializes poses only when referenced and has the parent-authorized
192 MiB temporary storage ceiling. The working-memory ceiling remains 256 MiB.

## Completed parent run

The revised emitter completed successfully in 55.275 seconds at 70,400 KiB
peak RSS. Its 109,912,064-byte SQLite scratch file was removed; 44,417,051 bytes
of outputs remain. The actual emitted row/pose source is **143,145 lines in
44 modules**. The additional 5,645 blocks, 17,651 unique relaxation edges,
12,933 contexts and remaining semantic contracts currently live in JSON/JSONL;
they are not already converted proofs hidden inside that line total.

The selected pair scopes total 635,162 distinct historical declarations. The
extractor checked their entire source/neighbor/target bindings, including 256
reused C701 plans, 59 reused C973 plans and 128 reused C978 plans. It omitted
16,513 unused imported pair declarations. This is a successful exact data
assembly and ancestry check, not Lean acceptance of those six whole cases.
