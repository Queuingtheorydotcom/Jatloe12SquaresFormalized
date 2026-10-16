# Complete historical overlap groups

The producer `scripts/prepare_historical_common_groups.py` consumes the exact
audited rectangular partitions of the 113 original pair stages. Its default
selection is C713's nine pair stages; `--cases all` selects all six historical
cases. `--fused` writes a separate `HistoricalCommonFused` proposal and removes
all imports of the old standalone fan modules. It produces an isolated
proposal, not an acceptance receipt.

## Semantic boundaries

Each stage keeps its original ordered blocked source plans and its complete
original neighbor domain. A semantic context retains the actual pose ID and
actual pruning block. Sharing a raw fan does **not** select a representative
pose: different original uses check their own exact input and integer
reference identities before applying the same raw certificate.

`IndexedCommonGroups.Context` has two alternatives:

- A fan linked to the existing `IndexedRawPairPlans.PoseContext`, including
  actual source-row membership, a valid original reference, and an exact
  proof-free numeric cache.
- An explicit checked `EmptyContext.Witness` on the actual block and original
  pose rows. This is used for context 4318; a missing fan never implies empty.

Every rectangle is either checked by one common point (each participating
square checks its own four faces) or by the original eight actual axes for
every pair in that rectangle. Strictness is retained by the original integer
checkers. A separate finite range check proves that every source/neighbor pair
is covered by at least one checked rectangle. The updated producer uses
`CommonRectanglePartition`: binary subdivision proves this coverage by
induction in the number of rectangles, rather than checking all pose pairs.

`CommonGroupPruning.block_overlap` then matches each original blocked plan's
source and complete block, proves the exact neighbor list is retained, and
returns the original direct-pruning `BlockOverlap` obligation. It introduces
no new packing premise.

## Source sharing and replay

The initial prototype stores one cache command per used raw fan and one
binding command per distinct actual pose/block use. Its producer completed,
but its 60,840 lines are not intended for final activation. The fused route
stores one cycle recipe that creates the raw proof, numeric cache, and actual
context together. The completed fused producer reports 43,466 lines in 1,540
modules: 12,932 canonical fan bindings, 336 additional authentic bindings, one
explicit empty binding, and 3,392 rectangle records. It has no imports of the
old standalone fan modules. Every group uses one rectangle record. Neither route stores
records indexed by source/neighbor pairs. Commands
only emit ordinary definitions and separately checked proof declarations;
numeric facts use the existing bounded `kernel_matrix` implementation and
ordinary `decide +kernel`.

The producer caps its own memory at 256 MiB, work time at 115 seconds, and
proposal size at 16 MiB; it runs no compiler or geometric search. It checks
input hashes against the preceding exact audit and records all produced
hashes. Production activation and Lean replay belong to the coordinator.

The small `Compact.HistoricalCommon.Pilot` proves only one authentic original
blocked-source/neighbor overlap. Completion of a case requires all its groups,
direct-pruning plans, original ownership entrances, and any chord transitions
to be replayed and assembled.

The coordinator reported acceptance of `IndexedCommonPoint`,
`IndexedCommonGroups`, and `IndexedCommonContext`. The fused command and its
four authentic contexts also passed, in 9.882 and 13.430 seconds respectively,
under the 400 MiB physical-footprint guard. The context pilot is not acceptance
of the complete 12,932-context collection or of a whole case.

Source inspection distinguishes two costs: `RawContext.Check` quantifies only
over stored fan entries and checks membership, copied rows, and integer vertex
identities; it does not quantify over all 768 directions. The direction table
is consulted by binary search when constructing untrusted lookup hints.
Consequently, a full replay estimate must distinguish constructor normalization
from kernel checking before attributing the pilot time to geometric proof size.
The rectangle helper's first replay required a noncomputable recursive decision
instance and explicit zero-addition simplification. Its latest verification log
reports both soundness theorems with ordinary axioms only. The complete stage
collection still needs replay.

An inventory of the existing group metadata identifies 2,044 common-point
groups and 1,348 axis-fallback groups. Of the 12,933 total contexts, 2,703 occur
only in common-point groups, so a future four-own-face specialization can avoid
their full support fans. No such specialization is assumed by the current
proposal or counted as an achieved source/runtime saving.
