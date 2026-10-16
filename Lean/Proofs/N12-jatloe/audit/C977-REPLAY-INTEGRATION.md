# C977 replay and integration boundary

This is a source audit, not a new case exclusion. The bounded replay is owned by the parent worker.

## Exact replay roots

1. `Completion.Cases.C977.PoseEnclosure`: 11 local modules, 910 source lines; no missing local dependency or historical native check.
2. `Completion.Cases.C977.BorderPoints`: 14 local modules, 1,451 source lines; no missing local dependency or historical native check.
3. `Completion.Cases.C977.AuxiliaryContext`: 83 local modules, 11,316 source lines, full source closure present. This imports the shared baseline through `S12.PackingConstant`; its closure contains 723 inherited `native_decide` sites. C977 adds none. The baseline trust model must be reported explicitly; a source-only replay plan does not validate those checks.
4. `Compact.Bridge.C977DisjointChain`: 12 local modules, 1,385 source lines; current-source hashes were already accepted at the audit snapshot. Original-square separating-axis soundness is discharged; case enclosure hypotheses remain.

The root closure figures are a snapshot, not a claim about extra source needed, Mathlib size, or how many modules still need recompilation. `evidence/c977-replay-plan.json` records the exact topological orders and accepted-source-hash snapshot.

## What is actually proved by the existing C977 source

`canonical_auxiliary_context_cover` preserves the original normalized packing, permitting only the proved transpose symmetry. It produces the strengthened missing-corner facts, canonical corner bounds, one closed wall branch, and the entire actual 12-owner vector among 57 exhaustive vectors. There are 16 closed wall branches; equality belongs to both half-spaces.

`excludes_case_of_auxiliary_contexts` is the exact whole-case assembly theorem. Its missing argument is a geometric contradiction for each actual packing satisfying all these facts. It does not claim that any of the 912 contexts has been excluded.

## Critical vector-index correspondence

The research and Lean domains are equal, in the same order. The complete vectors are also equal as sets, but the research verifier sorts the vector list while Lean retains recursive domain enumeration order. The six research residual IDs `[0,8,12,20,25,29]` correspond to Lean IDs `[0,8,10,20,23,27]`. In particular, the research vector29 wall-chain tree belongs to **Lean vector27**, not Lean vector29.

`evidence/c977-vector-index-map.json` contains all 57 indices in both directions, the entire six residual vectors, and source digests. This comparison used only tiny exact integer list/set calculations; it is not a Lean proof of index conversion. A Lean integration must either prove this conversion or avoid index dependence by stating the full vectors.

Research sign indices use bit k to select sign +1, with owner slots `[8,9,10,11]` and axes `[y,x,y,x]`. With the stated clipping inequality `sign*coordinate <= sign*2`, Lean's Boolean wall branch is precisely the bit value (true selects coordinate≤2). Retain equality on both sides. Authenticate the exact historical clipping implementation before promoting this source correspondence to a formal adapter.

## What the shared DAG can and cannot replace

`scripts/c977_plan_dag.py` shares operation prefixes only when the full initial state agrees: resolution, wall-sign index, and initial vector subset. It retains target vector subsets, excluded subsets, terminals, and complete center trees. Exact JSON reconstruction passes. It reduces 5,619 selectors to 4,413, using 20 initial-state groups and 11 derivation nodes.

This is a lossless representation of an unfinished research plan. There is no existing Lean 5,619-selector geometric proof for it to replace. The existing `AuxiliaryContext` proof establishes exhaustive coverage; replacing that with the research JSON would discard a proved obligation rather than simplify it. Keep the current coverage proof.

For future continuous exclusion, each forward DAG edge must have a sound original-square enclosure rule. `Compact.Core.Dag.derive` can share facts along its parent ancestry. Refutation dependencies have the opposite logical direction and need explicit terminal coverage and an appropriate topological ordering; applying the generic refutation combinator blindly to forward enclosure edges is invalid.

## Concrete whole-obligation targets

The exact research plan partitions the missing exclusion into these obligations:

- Fifteen nonzero wall signs covering all 57 vectors. Twelve assert empty initial domains; signs4,8,12 also have respectively53,28,30 pruning selectors. Prove each initial-domain enclosure and emptiness; a zero-operation plan is not a zero-proof obligation.
- Sign0 initial shared pruning excludes 51 vectors in 758 selectors. The six residual vectors are exactly those mapped above.
- Research residual0,8,12: border-conflict terminals. Residual20: missing-point conflict. Residual25: empty-domain terminal. Residual29: a seven-node/four-leaf center tree with two chain terminals and two border/strip terminals.

A promising concrete integration is the residual29 chain: for original ordered owners0,9,2, the accepted chain theorem gives `centerX owner0 < 3/2` once the actual common side, near-axis normals, common height band of width≤43/100, forward/transverse gap bounds, disjointness and final wall containment are supplied. The tree's opposite branch is `3/2 ≤ centerX owner0`. The remaining mathematics is the universal enclosure certificate that gives those bounds for that complete vector and tree branch. It has not been supplied by the JSON. The accepted theorem no longer assumes a separating-axis axiom.

No new whole C977 context exclusion is claimed by this audit or the DAG conversion.
