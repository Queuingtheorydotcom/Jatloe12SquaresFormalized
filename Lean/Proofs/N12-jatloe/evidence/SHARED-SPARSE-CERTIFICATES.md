# Shared sparse integer certificate pilot

The reusable checker is `Compact/Core/SparseInteger.lean`. It supports any
finite number of weighted rows, so it covers the three- and four-row empty
certificates recovered for C898. It stores a row dictionary once and uses
integer weight/index pairs. A positive target scale clears denominators.
Numerical checks contain only integer arithmetic and Boolean strictness.
The soundness theorem uses the original `S12.LinearConstraint.Holds` through
the existing positive-denominator normalization bridge.

`SparseInteger.replay` proves a topologically indexed row derivation directly.
Each certificate cites earlier row indices; each node's numerical check can
be an opaque theorem reused by all consumers. There is no DAG-to-tree
expansion, no rational linear-system solving during replay, and no native
evaluation oracle. Different geometric branches must still establish their
own initial assumptions. Equal row bytes do not justify sharing a proof
between incompatible branch contexts.

## Complete migrated C696 obligation

`Compact/Core/C696Pose117.lean` proves all centre inequalities of saved target
pose 117 from source pose 0 of `RootOneStep000Data.lean`. Both angular indices
are 0. Original row numbers 0–8 and 802–805, their denominators and strictness,
and both complete row-occurrence lists are retained exactly.

The saved target has 15 row occurrences. Four need new numerical proofs;
eleven are source-row aliases, including repeated occurrences. The migration
therefore replaces 15 support replay records with four checked integer
certificates and direct aliases: **11/15 fewer numerical support checks**.
There are 10 weighted term occurrences instead of 21 support/slack terms.
No rational Cramer weights are reconstructed by Lean.

The old data already had a dictionary containing these 13 distinct rows.
This pilot does **not** claim a further reduction in that literal row table.
Its demonstrated reduction is in repeated proof checking. It is one full
saved pose-row implication, not the entire propagation step or C696 case.

## Authentic migrated C898 empty leaf

`Compact/Core/C898EmptyLeaf.lean` uses owner 0, angular root 0, path `YYYNYYN`
from the recovered `evidence/C898/raw/data/region898.json`. Four rows with
their original positive denominators sum to zero with nonnegative integer
weights, including positive weights on strict rows. The checker establishes
the entire leaf contradiction using the original row predicates.

The 704 initial trees have 10,149 empty certificates: 4,493 have three rows
and 5,656 have four. The new checker handles both arities. The independent
schema audit also found all 3,522 forbidden blocks are literal ancestor
positive-cut subsets. Their 14,088 implication certificates can be replaced
by a generic context-membership rule once that branch checker is implemented.
This is distinct from deduplicating numerical rows.

The leaf pilot does not prove the initial-tree ancestry, the complete initial
cover, or any of the 15 propagation rounds needed for the whole C898 case.
The subsequent witnesses were not present in the recovered region JSON.

## Validation and conversion gates

`scripts/audit_shared_sparse.py` checks the authentic file hashes, every
C696 copied coefficient and denominator, both pose lists, exact new weights,
and the exact C898 strict-zero sum. Its recorded run took 0.103 seconds and
110,133,248 bytes peak RSS on macOS, without children, solvers, downloads or
compilation. Detailed evidence is `evidence/shared-sparse-pilots.json`.

Lean validation is performed separately by the root worker, with receipts in
`.verification/`. Exact Python identities alone are not kernel validation.

Before converting an entire case, implement and validate branch ancestry,
positive/negative cut coverage, forbidden-block context membership, and
direct reference replay. Preserve geometric checker soundness and strict
inequalities. Profile one complete initial owner cover before deciding the
batch/module size. Later propagation still needs authentic witnesses or new
proved geometric arguments; a smaller row representation cannot supply them.
