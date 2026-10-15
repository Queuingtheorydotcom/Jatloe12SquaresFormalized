import S12.LinearCertificate

/-!
# Direct sparse certificates in the original S12 enclosure model

Unlike the legacy basis decoder, this checker consumes explicit rational
weights and source indices. It constructs only the selected linear combination:
no `RegionTree`, inferred Cramer coefficients, domain copies, or pose decoder.
The result is exactly `S12.LinearConstraint`; strictness is inherited through
the original `scale` and `add` operations, not a replacement geometry model.
-/

namespace N12Compact.DirectLinear

open S12

abbrev Terms := List (ℚ × Nat)

/-- Invalid indices fail. Only referenced rows enter the weighted sum. -/
def combine {n : Nat} (rows : List (LinearConstraint n)) :
    Terms → Option (LinearConstraint n)
  | [] => some (LinearConstraint.zero n)
  | (weight, index) :: rest => do
      let row ← rows[index]?
      let tail ← combine rows rest
      return (row.scale weight).add tail

/-- Closed exact arithmetic obligation, intended to be discharged once and
then reused as an opaque theorem. All source weights must be nonnegative. -/
def Check {n : Nat} (rows : List (LinearConstraint n)) (terms : Terms)
    (target : LinearConstraint n) : Prop :=
  (∀ term ∈ terms, 0 ≤ term.1) ∧ combine rows terms = some target

instance {n : Nat} (rows : List (LinearConstraint n)) (terms : Terms)
    (target : LinearConstraint n) : Decidable (Check rows terms target) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem combine_sound {n : Nat} (rows : List (LinearConstraint n))
    (terms : Terms) (target : LinearConstraint n) (x : Fin n → ℝ)
    (nonnegative : ∀ term ∈ terms, 0 ≤ term.1)
    (inputs : ∀ row ∈ rows, row.Holds x)
    (checked : combine rows terms = some target) : target.Holds x := by
  induction terms generalizing target with
  | nil =>
      have he : LinearConstraint.zero n = target := Option.some.inj checked
      rw [← he]
      simp [LinearConstraint.zero, LinearConstraint.Holds]
  | cons term rest ih =>
      rcases term with ⟨weight, index⟩
      cases hrow : rows[index]? with
      | none => simp [combine, hrow] at checked
      | some row =>
          cases htail : combine rows rest with
          | none => simp [combine, hrow, htail] at checked
          | some tail =>
              have he : (row.scale weight).add tail = target := by
                simpa [combine, hrow, htail] using checked
              rw [← he]
              apply LinearConstraint.holds_add
              · exact LinearConstraint.holds_scale weight row x
                  (nonnegative (weight, index) (by simp))
                  (inputs row (List.mem_of_getElem? hrow))
              · apply ih tail
                · intro term hterm
                  exact nonnegative term (List.mem_cons_of_mem _ hterm)
                · exact htail

/-- The checker establishes an actual original-model enclosure implication.
It does not merely compare certificate hashes or trust a numerical solver. -/
theorem Check.sound {n : Nat} {rows : List (LinearConstraint n)}
    {terms : Terms} {target : LinearConstraint n} (checked : Check rows terms target)
    (x : Fin n → ℝ) (inputs : ∀ row ∈ rows, row.Holds x) : target.Holds x :=
  combine_sound rows terms target x checked.1 inputs checked.2

/-- A sparse core suffices for any larger source domain containing its rows.
The subset proof is mandatory; selecting convenient unrelated rows is invalid. -/
theorem Check.sound_of_subset {n : Nat} {core inputs : List (LinearConstraint n)}
    {terms : Terms} {target : LinearConstraint n} (checked : Check core terms target)
    (subset : ∀ row ∈ core, row ∈ inputs) (x : Fin n → ℝ)
    (holds : ∀ row ∈ inputs, row.Holds x) : target.Holds x :=
  checked.sound x (fun row hrow => holds row (subset row hrow))

def contradiction (n : Nat) : LinearConstraint n := ⟨Affine.zero n, true⟩

/-- Complete strict-zero contradiction, including strictness checks. -/
theorem Check.refutes {n : Nat} {rows : List (LinearConstraint n)} {terms : Terms}
    (checked : Check rows terms (contradiction n)) :
    ¬ ∃ x : Fin n → ℝ, ∀ row ∈ rows, row.Holds x := by
  rintro ⟨x, hx⟩
  have impossible := checked.sound x hx
  simpa [contradiction, LinearConstraint.Holds] using impossible

end N12Compact.DirectLinear
