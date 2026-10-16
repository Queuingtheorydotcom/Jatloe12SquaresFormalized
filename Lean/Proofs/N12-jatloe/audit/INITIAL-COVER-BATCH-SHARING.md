# Shared initial-cover batches

`InitialCoverBatch.lean` replaces repeated batch declarations with one common
command. The command preserves each original named entry and invokes the
already established `checked_recipe` command separately for every record.
The original eight independent numeric facts remain opaque theorem constants.
A generic list-cons proof assembles the batch; no combined arithmetic decision
or larger numerical accumulator is introduced.

The producer `scripts/compact_initial_batches.py` completed with 856 batches
and all 6,848 original records: 624 batches from the five shared-query entrance
proposals, 144 from active C713, and 88 from active C898. It checks each original
entry name, record text, ordered batch list, individual proof list, common
point premises, and final semantic acceptance bridge before replacing source.

The proposal contains 13,696 Lean lines. It removes 16,064 lines of repeated
batch scaffolding; including the new generic helper, the measured combined
import closure of all seven original-owner entrance modules decreases by
15,989 lines. This counts actual imported project source and excludes external
library sources. The before/after module lists and hashes are recorded in
`evidence/proposals/InitialBatchSharing/manifest.json`.

This is a changed-files-only overlay on
`evidence/proposals/HistoricalInitialSharedQueries` plus active C713 and C898.
It does not replace ownership hypotheses, target pose IDs, missing-angle
empty certificates, angle coverage, or final owner theorem statements. The
authentic eight-root pilot is `C898.RecipeInitial.BatchCommandPilot`. The helper
and pilot are source-complete but still await coordinator replay. A subsequent
one-line explicit Bool/Prop guard repair is recorded in the manifest's
`source_repairs`; the helper hash and closure record were refreshed. All 856
generated files, their hashes, and all line counts are unchanged.
