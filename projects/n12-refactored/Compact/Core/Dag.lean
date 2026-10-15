import Std

/-!
# Shared finite proof DAGs

This module imports only Lean's standard library. It contains no packing claim.
Nodes are numbered in dependency order. A local proof mentions only its direct
dependencies; the transitive soundness argument below is proved once.

`deriveOn` also justifies backward slicing: keep the root and every dependency
reachable from it, and no proof is required for a discarded node. In a branching
refutation every child is a dependency, so this does not discard split ties or
unproved alternatives. Geometric local rules and exhaustive covers remain
explicit obligations for the client.
-/

namespace N12Compact

/-- A finite directed acyclic graph. The order check concerns indices only;
it must be established by ordinary Lean proofs. -/
structure Dag (n : Nat) where
  dependencies : Fin n → List (Fin n)
  earlier : ∀ i j, j ∈ dependencies i → j.val < i.val

namespace Dag

variable {n : Nat} (g : Dag n)

/-- A retained set contains all dependencies of each node it contains. This is
the exact closure requirement for deleting irrelevant proof history. -/
def Closed (keep : Fin n → Prop) : Prop :=
  ∀ i, keep i → ∀ j, j ∈ g.dependencies i → keep j

/-- Shared soundness of a dependency-closed subgraph. Unlike a linear replay,
this requires each retained local implication only once, even when several
later nodes use it. -/
theorem deriveOn (claim : Fin n → Prop) (keep : Fin n → Prop)
    (closed : g.Closed keep)
    (localProof : ∀ i, keep i →
      (∀ j, j ∈ g.dependencies i → claim j) → claim i) :
    ∀ i, keep i → claim i := by
  have proved : ∀ k : Nat, ∀ i : Fin n, i.val = k → keep i → claim i := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i hi hkeep
        apply localProof i hkeep
        intro j hj
        have earlier : j.val < k := by
          rw [← hi]
          exact g.earlier i j hj
        exact ih j.val earlier j rfl (closed i hkeep j hj)
  intro i hi
  exact proved i.val i rfl hi

/-- The unpruned graph is the special case retaining every node. -/
theorem derive (claim : Fin n → Prop)
    (localProof : ∀ i, (∀ j, j ∈ g.dependencies i → claim j) → claim i) :
    ∀ i, claim i := by
  intro i
  exact g.deriveOn claim (fun _ => True) (fun _ _ _ _ => True.intro)
    (fun j _ => localProof j) i True.intro

/-- A selected contradiction depends only on its retained dependency closure.
The unretained nodes need not have either proofs or computed certificates. -/
theorem conflictOn (claim : Fin n → Prop) (keep : Fin n → Prop)
    (closed : g.Closed keep)
    (localProof : ∀ i, keep i →
      (∀ j, j ∈ g.dependencies i → claim j) → claim i)
    (root : Fin n) (root_kept : keep root) (conflict : claim root → False) :
    False :=
  conflict (g.deriveOn claim keep closed localProof root root_kept)

/-- A refutation node denotes a set of configurations. Its dependency list is
an exhaustive list of possible successors. The successor configuration may
change, allowing a proved symmetry or normalization rule. An empty list must
be justified by an actual contradiction. Descending indices exclude cycles. -/
theorem refuteOn {State : Type u} (holds : Fin n → State → Prop)
    (keep : Fin n → Prop) (closed : g.Closed keep)
    (cover : ∀ i, keep i → ∀ x, holds i x →
      ∃ j, j ∈ g.dependencies i ∧ ∃ y, holds j y) :
    ∀ i, keep i → ∀ x, ¬ holds i x := by
  apply g.deriveOn (fun i => ∀ x, ¬ holds i x) keep closed
  intro i hi previous x hx
  obtain ⟨j, hj, y, hy⟩ := cover i hi x hx
  exact previous j hj y hy

theorem refute {State : Type u} (holds : Fin n → State → Prop)
    (cover : ∀ i x, holds i x →
      ∃ j, j ∈ g.dependencies i ∧ ∃ y, holds j y) :
    ∀ i x, ¬ holds i x := by
  intro i
  exact g.refuteOn holds (fun _ => True) (fun _ _ _ _ => True.intro)
    (fun j _ => cover j) i True.intro

/-- Interface to an exact local certificate checker. `Check` may be a decidable
proposition, but this theorem neither computes checks nor grants an oracle.
Every check and the checker-soundness theorem must be supplied separately.
Keeping those proofs opaque lets many nodes share the same semantic theorem. -/
theorem checkedRefuteOn {State : Type u} {Certificate : Type v}
    (holds : Fin n → State → Prop) (keep : Fin n → Prop)
    (closed : g.Closed keep) (cert : Fin n → Certificate)
    (Check : Fin n → Certificate → List (Fin n) → Prop)
    (checked : ∀ i, keep i → Check i (cert i) (g.dependencies i))
    (checker_sound : ∀ i c children, Check i c children →
      ∀ x, holds i x → ∃ j, j ∈ children ∧ ∃ y, holds j y) :
    ∀ i, keep i → ∀ x, ¬ holds i x := by
  apply g.refuteOn holds keep closed
  intro i hi
  exact checker_sound i (cert i) (g.dependencies i) (checked i hi)

end Dag

end N12Compact
