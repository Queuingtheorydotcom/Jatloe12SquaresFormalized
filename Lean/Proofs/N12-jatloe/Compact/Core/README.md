# Compact proof core

These modules are generic mathematics, not a proof of any twelve-square case.
They do not redefine packing, introduce an axiom, or approve numerical output.

## Shared dependency proofs

`Dag.lean` imports only `Std`. `Dag.deriveOn` proves a finite collection of claims
from their checked direct dependencies, with one shared induction over node
indices. `Dag.conflictOn` extracts a selected contradiction.

A dependency-closed retained set justifies backward slicing from that
contradiction. Discarded nodes do not need certificates or semantic proofs.
This is useful for removing enclosure updates and constraints never used by a
final conflict. For refutation trees every alternative is a dependency: pruning
does not mean keeping only the convenient side of a geometric split.

`Dag.refuteOn` handles exhaustive covers, including covers that apply a proved
symmetry to a configuration. `Dag.checkedRefuteOn` connects an external exact
local checker to the same soundness theorem. Its `checked` and
`checker_sound` hypotheses remain explicit. Client modules must supply both.

Store each shared node and its proof once. Reference predecessor indices or
opaque theorem names. Do not reconstruct a large domain expression at every
descendant, and do not expand the transitive ancestor tree into the term for
each root.

## Symbolic replacement of propagation

`LinearCombination.lean` uses ordered commutative rings and finite sums from
Mathlib. `sparseCombination_refutes` consumes only the selected source rows and
their nonnegative weights. `strictCombination_refutes` permits one positively
weighted strict inequality and an exactly zero total; no numerical epsilon is
needed. An exact sum identity must be proved separately.

`contraction_bound` replaces iteration of `x ≤ a*x+b` by `(1-a)*x ≤ b`.
`contraction_refutes` closes the case when `x>0`, `a<1`, and `b≤0`.
`twoNodeCycle_refutes` directly closes `x≤a*y`, `y≤b*x`, `a≥0`, `a*b<1`,
and `x>0`. Longer cycles can first be collapsed symbolically. These lemmas do
not establish that any current packing branch satisfies those inequalities.

## Validation boundary

Source was assembled for Lean 4.19 without running a compiler in this worker.
The Std-only DAG module can be checked without a Mathlib restore. The algebra
module still requires the pinned Mathlib dependency and its own replay.
Neither source inspection nor successful generic-core replay proves a packing
case, supplies missing coverage, or validates a generated certificate.

## Direct original-model checker and authentic fixture

`DirectLinear.lean` imports the preserved `S12.LinearCertificate` and uses its
actual `LinearConstraint`, strictness rules, and real-valued `Holds` predicate.
Its `combine` follows sparse row indices and exact rational weights, rejecting
missing rows. `Check.sound` proves the resulting original-model implication;
`Check.sound_of_subset` permits a proved subset of a larger source domain;
`Check.refutes` handles strict-zero contradictions.

`C696SupportFixture.lean` migrates an actual implication from C696 root one's
first action: source pose 0, target pose 117, target row position 5. Its numerical
check uses only the two source rows that contribute to that row, while a proved
subset lemma connects them to the original twelve-row source. It removes the
basis decoder, Cramer calculation, pose-table decoder, and region-tree path
from this local implication. The source module has 826 stored raw rows and 120
poses covering many additional obligations; their removal from this fixture
must not be reported as compression of the entire action.

The exact old-source hash, selected row IDs, literal rows, and weights are in
`evidence/c696-direct-linear-fixture.json`. Python exact arithmetic confirms
both coefficients and the constant. Lean compilation remains the parent's
separate validation step. A final case adapter must still connect this fixture
to its original source/target pose tables and establish all other coverage.

## Integer support gate

`IntegerSupport.lean` provides a two-row certificate whose closed check uses
integer signs, three integer coefficient identities, and boolean strictness.
The generic soundness proof converts this relation to real inequalities, then
uses positive-denominator normalization to recover the exact original
`S12.LinearConstraint.Holds` statement. A strict target requires a positive
weight on an actually strict source; no strictness is manufactured.

`IntegerSupportCase.lean` checks the same authentic C696 implication using
`1605785*A + 891537427849*B = 608202928986*T` on the raw numerator rows.
The coefficient checks contain no rational comparison. Its final theorem
retains the original three denominators. The fixture imports neither the
rational fixture nor any large certificate table. The exact record and
comparable serialized primitive sizes are in
`evidence/c696-integer-support-fixture.json`; timing and Lean acceptance remain
separate parent-run checks.
