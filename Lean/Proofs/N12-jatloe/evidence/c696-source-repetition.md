# C696 exact repetition and checker-cost audit

Status: completed source audit, not Lean verification. Machine-readable evidence:
`c696-source-repetition.json`. Reproduce with `scripts/profile_repetition.py`
against the local C696 source directory. The original source was read only.

## Measured results

The audit streamed all 305 files matching `**/*Data.lean`: 243,903,387 bytes and
2,486,236 lines. It took 11.161 seconds, used 36,814,848 bytes peak RSS, and used
a temporary SQLite database of 90,165,248 bytes. The database was removed on
exit. The process has terminated. SHA-256 in the JSON authenticates the ordered
relative file names and their individual source hashes.

| Entry family | Occurrences | Exact distinct entries | Duplicate literal bytes |
| --- | ---: | ---: | ---: |
| Raw affine rows | 1,398,394 | 503,684 | 56,544,383 |
| Angle entries | 19,200 | 192 | 697,059 |
| Direction vectors | 28,196 | 290 | 418,795 |
| Raw poses | 59,198 | 30,826 | 1,883,105 |
| Support recipes | 574,008 | 102,351 | 9,048,509 |
| Raw tree nodes | 96,009 | 86,151 | 4,587,832 |

Entries were compared by complete source bytes, excluding only line endings.
No rational normalization, scaling equivalence, or semantic pose comparison was
used. This deliberately misses additional possible sharing.

An independent whole-declaration audit found 19,140,160 repeated source bytes,
occupying 290,057 lines. Every hash match was checked byte-for-byte. These savings
overlap with the entry-level table and must not be added to it. The largest exact
duplicate is the 978,919-byte `rawRows` declaration shared by root-one step 18
and root-zero step 18.

For raw affine rows alone, storing one exact literal per distinct row and
allowing eight bytes per original row reference would use approximately
45,067,790 bytes instead of 90,425,021 bytes. This is a genuine data-sharing
change, not shorter formatting. It removes roughly half the row payload but
only **18.6% of total Data-file bytes**, before accounting for adapters and
proofs. It cannot by itself reach a 300,000-line assembled proof.

Raw poses, support recipes, and tree nodes use indices into *local* tables.
Identical entry text across two files does not necessarily denote the same
semantic object. Those entries cannot safely be interned globally until every
dependency has been rebased and authenticated. Equal affine-row literals have
no such local-index dependency; their strictness bit must remain part of the key.

## What the current code already supplies

The original project already contains useful shared infrastructure:

- `CompactTrace.Checker.checkRoot_sound` validates a finite acyclic trace with
  shared predecessors and requires both children of every split.
- `CompactGeometry.State.updateOwner` changes one owner's domain persistently.
  `State.realizes_updateOwner` and `CompactPair.Action.preserves_state` prove
  that the untouched domains and compulsory hulls remain valid.
- `Compact/emit_shared_rows.py` already supports exact row interning across
  one vector. It verifies local-to-global row maps, including strictness.

These existing mathematical interfaces should be reused. Merely introducing a
second generic DAG does not address the measured source or checking cost.

## Where repetition is reintroduced

`Compact/emit_pair.py` normally writes fresh row, angle, and pose tables for
each action. It writes an independently decoded plan per source pose and a
large closed `action.Check ... := by decide` proof. Sharing raw-row tables is
optional and is not used by the audited C696 material.

`Compact/BasisData.decodeTreeBudget` reads shared raw node indices but creates a
fresh recursive `RegionTree`; a cut recursively decodes both children. The
emitter even computes the *expanded* node count to give the decoder its budget.
Thus a raw DAG can become a tree again before the semantic check.

`CompactPruning.Plan.Check` then checks that expanded tree and traverses its
leaves to verify all relaxations. `Basis.decode` reconstructs rational support
coefficients; those candidates are subsequently checked again by the original
checker. C696's `RootOne.lean` additionally proves large decoded source/neighbor
domain equalities by closed reduction at each transition, despite using a
persistent `updateOwner` at the semantic level.

## Sound persistent representation to implement next

1. Keep exact immutable row, angle, and pose tables with stable identities.
   Decode a newly introduced row once and prove its lookup/evaluation theorem.
   Poses reference the canonical row IDs, not action-local table positions.
2. Give each owner domain an immutable version ID. A pair action consumes the
   exact source-owner and neighbor-owner version IDs and introduces only its
   target version. Other owners retain their IDs through `updateOwner`.
   Establish those lookup equations from update lemmas rather than comparing
   fully decoded domain lists by `decide`.
3. Check a cut node against a named input-context ID. A valid sharing key must
   include its assumptions: the same tree code under different constraints is
   not automatically the same theorem. Represent a new context by a parent ID
   and an added row; prove the context-membership implication once.
4. Store sparse contradiction/support witnesses and checked local semantic
   implications as opaque theorems. The final trace composes theorem names;
   it does not rerun the numerical checker or expand shared subtrees.
5. Slice backward from the final conflict through *actual* row/pose/owner
   dependencies before emitting the final artifact. Retain exhaustive initial
   coverage and both closed split children. Use symbolic contraction arguments
   to eliminate whole propagation histories where their hypotheses can be
   proved. This is needed in addition to interning.

## Unresolved integration and validation obligations

The following are not accomplished by this audit: a sound indexed primitive
checker replacing `RegionTree` expansion; an exact global reindexing proof for
poses, supports and inherited Farkas indices; a backward slice that preserves
coverage; a completed missing root or case; or a measured compilation speedup.

Large opaque tables can still be repeatedly unfolded by kernel reduction.
Therefore a shared-table prototype must be checked on a complete representative
obligation, measuring total elaboration time and peak memory, before conversion
of the entire corpus. Source bytes and module counts alone are insufficient.
