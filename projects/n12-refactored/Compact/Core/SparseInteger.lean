import Compact.Core.IntegerSupport

/-!
# Shared sparse integer certificates

The row dictionary is supplied once. A certificate stores only row indices,
integer weights, and a positive integer target scale. Checking does not solve
a linear system and uses no rational comparison. The recursive sum is over
the few cited rows, not over an enclosure or its proof ancestry.

`replay` checks a topologically numbered derivation directly. It never unfolds
a DAG into a tree. Every node has an independent checked implication, so its
semantic proof can be shared by all later users. Initial-row assumptions and
strictness are preserved explicitly; this module makes no packing claim.
-/

namespace N12Compact.SparseInteger

open IntegerSupport

abbrev Terms (n : Nat) := List (Int × Fin n)

def zero : Row := ⟨0, 0, 0, false⟩

def sum {n : Nat} (rows : Fin n → Row) : Terms n → Row
  | [] => zero
  | (weight, index) :: rest =>
      let tail := sum rows rest
      ⟨weight * (rows index).x + tail.x,
        weight * (rows index).y + tail.y,
        weight * (rows index).constant + tail.constant,
        (decide (0 < weight) && (rows index).strict) || tail.strict⟩

def Nonnegative {n : Nat} (terms : Terms n) : Prop :=
  ∀ term ∈ terms, 0 ≤ term.1

instance {n : Nat} (terms : Terms n) : Decidable (Nonnegative terms) :=
  inferInstanceAs (Decidable (∀ term ∈ terms, 0 ≤ term.1))

theorem zero_holds (p : Fin 2 → ℝ) : zero.Holds p := by
  simp [zero, Row.Holds, Row.eval]

private theorem cons_checked {n : Nat} (rows : Fin n → Row)
    (weight : Int) (index : Fin n) (rest : Terms n) (hw : 0 ≤ weight) :
    (⟨weight, 1, 1⟩ : TwoRow).Check (rows index) (sum rows rest)
      (sum rows ((weight, index) :: rest)) := by
  refine ⟨hw, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (0 : Int) ≤ 1
    decide
  · change (0 : Int) < 1
    decide
  · dsimp [sum]
    ring
  · dsimp [sum]
    ring
  · dsimp [sum]
    ring
  · intro hstrict
    have cases : (0 < weight ∧ (rows index).strict = true) ∨
        (sum rows rest).strict = true := by
      simpa only [sum, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        using hstrict
    rcases cases with h | h
    · exact Or.inl h
    · exact Or.inr ⟨by change (0 : Int) < 1; decide, h⟩

theorem sum_sound {n : Nat} (rows : Fin n → Row) (terms : Terms n)
    (nonnegative : Nonnegative terms) (p : Fin 2 → ℝ)
    (holds : ∀ term ∈ terms, (rows term.2).Holds p) :
    (sum rows terms).Holds p := by
  revert nonnegative holds
  induction terms with
  | nil => intro _ _; exact zero_holds p
  | cons term rest ih =>
      intro nonnegative holds
      rcases term with ⟨weight, index⟩
      have hw : 0 ≤ weight := nonnegative (weight, index) (by simp)
      apply (cons_checked rows weight index rest hw).sound p
      · exact holds (weight, index) (by simp)
      · apply ih
        · intro term hterm
          exact nonnegative term (List.mem_cons_of_mem _ hterm)
        · intro term hterm
          exact holds term (List.mem_cons_of_mem _ hterm)

structure Certificate (n : Nat) where
  terms : Terms n
  scale : Int
  deriving DecidableEq

/-- The final two-row check compares the sparse sum with a positive multiple
of the target. The second row is zero, with weight zero. Reusing its soundness
theorem avoids a second implementation of real strict-sign reasoning. -/
def Certificate.Check {n : Nat} (certificate : Certificate n)
    (rows : Fin n → Row) (target : Row) : Prop :=
  Nonnegative certificate.terms ∧
    (⟨1, 0, certificate.scale⟩ : TwoRow).Check
      (sum rows certificate.terms) zero target

instance {n : Nat} (certificate : Certificate n) (rows : Fin n → Row)
    (target : Row) : Decidable (certificate.Check rows target) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Certificate.Check.sound {n : Nat} {certificate : Certificate n}
    {rows : Fin n → Row} {target : Row}
    (checked : certificate.Check rows target) (p : Fin 2 → ℝ)
    (holds : ∀ term ∈ certificate.terms, (rows term.2).Holds p) :
    target.Holds p :=
  checked.2.sound p (sum_sound rows certificate.terms checked.1 p holds)
    (zero_holds p)

/-- Original normalized row semantics. Denominators belong to the dictionary,
not the certificate; each source requires only its own positive denominator. -/
theorem Certificate.Check.normalized_sound {n : Nat}
    {certificate : Certificate n} {rows : Fin n → Row} {target : Row}
    (checked : certificate.Check rows target) (den : Fin n → Nat)
    (targetDen : Nat) (positive : ∀ i, 0 < den i) (targetPositive : 0 < targetDen)
    (p : Fin 2 → ℝ)
    (holds : ∀ term ∈ certificate.terms,
      ((rows term.2).normalized (den term.2)).Holds p) :
    (target.normalized targetDen).Holds p := by
  apply (target.normalized_holds_iff targetDen targetPositive p).mpr
  apply checked.sound p
  intro term hterm
  exact ((rows term.2).normalized_holds_iff (den term.2) (positive term.2) p).mp
    (holds term hterm)

/-- A complete local rule, either an authentic input assumption or an integer
certificate citing only earlier dictionary entries. Checks are proofs, and
can be declared once as opaque theorems instead of reduced repeatedly. -/
def Step {n : Nat} (rows : Fin n → Row) (input : Fin n → Prop) (i : Fin n) : Prop :=
  input i ∨ ∃ certificate : Certificate n,
    certificate.Check rows (rows i) ∧
    ∀ term ∈ certificate.terms, term.2.val < i.val

/-- Direct soundness of the shared row DAG. This does not decode or copy a
predecessor's derivation. Each real inequality is proved once by induction. -/
theorem replay {n : Nat} (rows : Fin n → Row) (input : Fin n → Prop)
    (steps : ∀ i, Step rows input i) (p : Fin 2 → ℝ)
    (initial : ∀ i, input i → (rows i).Holds p) : ∀ i, (rows i).Holds p := by
  have proved : ∀ k : Nat, ∀ i : Fin n, i.val = k → (rows i).Holds p := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
        intro i hi
        rcases steps i with hinput | ⟨certificate, checked, earlier⟩
        · exact initial i hinput
        · apply checked.sound p
          intro term hterm
          have hlt : term.2.val < k := by
            rw [← hi]
            exact earlier term hterm
          exact ih term.2.val hlt term.2 rfl
  intro i
  exact proved i.val i rfl

/-- An empty leaf is a strict zero row, proved by the same sparse checker. -/
theorem refutes {n : Nat} {certificate : Certificate n} {rows : Fin n → Row}
    (checked : certificate.Check rows ⟨0, 0, 0, true⟩) (p : Fin 2 → ℝ)
    (holds : ∀ term ∈ certificate.terms, (rows term.2).Holds p) : False := by
  have impossible := checked.sound p holds
  simpa [Row.Holds, Row.eval] using impossible

#print axioms Certificate.Check.normalized_sound
#print axioms replay

end N12Compact.SparseInteger
