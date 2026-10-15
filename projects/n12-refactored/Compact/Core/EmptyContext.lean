import Compact.Core.SparseInteger

/-! A missing support fan is never an emptiness proof. This small checker
requires an explicit nonnegative weighted contradiction from actual inputs. -/
namespace N12Compact.EmptyContext
open IntegerSupport SparseInteger

structure Witness (n : Nat) where
  inputs : List (Fin n)
  terms : Terms n

def Witness.Check {n : Nat} (rows : Fin n → Row) (w : Witness n) : Prop :=
  Nonnegative w.terms ∧
  (∀ term ∈ w.terms, term.2 ∈ w.inputs) ∧
  (sum rows w.terms).x = 0 ∧ (sum rows w.terms).y = 0 ∧
  ((sum rows w.terms).constant < 0 ∨
    ((sum rows w.terms).constant ≤ 0 ∧ (sum rows w.terms).strict = true))

instance {n : Nat} (rows : Fin n → Row) (w : Witness n) : Decidable (w.Check rows) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Witness.sound {n : Nat} (rows : Fin n → Row) (w : Witness n)
    (checked : w.Check rows) (p : Fin 2 → ℝ)
    (holds : ∀ i ∈ w.inputs, (rows i).Holds p) : False := by
  obtain ⟨weights, included, hx, hy, impossible⟩ := checked
  have hs : (sum rows w.terms).Holds p :=
    sum_sound rows w.terms weights p (fun term ht => holds term.2 (included term ht))
  have he : (sum rows w.terms).eval p = ((sum rows w.terms).constant : ℝ) := by
    simp only [Row.eval, hx, hy, Int.cast_zero, zero_mul, zero_add]
  rcases impossible with negative | ⟨nonpositive, strict⟩
  · have hn := Row.nonneg _ _ hs
    rw [he] at hn
    have hc : ((sum rows w.terms).constant : ℝ) < 0 := by exact_mod_cast negative
    exact (not_lt_of_ge hn) hc
  · have hp := Row.positive _ _ strict hs
    rw [he] at hp
    have hc : ((sum rows w.terms).constant : ℝ) ≤ 0 := by exact_mod_cast nonpositive
    exact (not_lt_of_ge hc) hp

end N12Compact.EmptyContext
