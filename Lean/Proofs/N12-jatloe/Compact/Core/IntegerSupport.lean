import S12.LinearCertificate
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integer certificates for two-row support

All arithmetic in `TwoRow.Check` is over integers and booleans. Positive
denominators are cleared before checking, so the kernel need not reduce an
opaque rational comparison or reconstruct rational Cramer coefficients.
Soundness is proved over the reals and connected to the unchanged original
`S12.LinearConstraint.Holds` predicate by positive-denominator normalization.
-/

namespace N12Compact.IntegerSupport

open S12

structure Row where
  x : Int
  y : Int
  constant : Int
  strict : Bool
  deriving DecidableEq

def Row.eval (r : Row) (p : Fin 2 → ℝ) : ℝ :=
  (r.x : ℝ) * p 0 + (r.y : ℝ) * p 1 + r.constant

def Row.Holds (r : Row) (p : Fin 2 → ℝ) : Prop :=
  if r.strict then 0 < r.eval p else 0 ≤ r.eval p

theorem Row.nonneg (r : Row) (p : Fin 2 → ℝ) (h : r.Holds p) :
    0 ≤ r.eval p := by
  cases hs : r.strict with
  | false => simpa only [Holds, hs, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
      have hp : 0 < r.eval p := by simpa only [Holds, hs, ↓reduceIte] using h
      exact hp.le

theorem Row.positive (r : Row) (p : Fin 2 → ℝ)
    (strict : r.strict = true) (h : r.Holds p) : 0 < r.eval p := by
  simpa only [Holds, strict, ↓reduceIte] using h

/-- Exactly the original normalized affine row, with the strictness bit
preserved. The denominator's positivity is required in the bridge theorem. -/
def Row.normalized (r : Row) (den : Nat) : LinearConstraint 2 :=
  ⟨⟨fun i => if i.val = 0 then (r.x : ℚ) / den else (r.y : ℚ) / den,
    (r.constant : ℚ) / den⟩, r.strict⟩

theorem Row.normalized_eval (r : Row) (den : Nat) (p : Fin 2 → ℝ) :
    (r.normalized den).form.eval p = r.eval p / den := by
  simp [normalized, Affine.eval, eval, Fin.sum_univ_succ, div_eq_mul_inv]; ring

theorem Row.normalized_holds_iff (r : Row) (den : Nat) (positive : 0 < den)
    (p : Fin 2 → ℝ) : (r.normalized den).Holds p ↔ r.Holds p := by
  have hd : (0 : ℝ) < den := by exact_mod_cast positive
  change (if r.strict then 0 < (r.normalized den).form.eval p
    else 0 ≤ (r.normalized den).form.eval p) ↔ r.Holds p
  rw [normalized_eval]
  cases hs : r.strict <;> simp [Holds, hs, le_div_iff₀ hd, lt_div_iff₀ hd]

structure TwoRow where
  left : Int
  right : Int
  scale : Int
  deriving DecidableEq

/-- The numerical checker has no rational or real operation. A strict target
also requires an actually strict source with a strictly positive weight. -/
def TwoRow.Check (w : TwoRow) (a b target : Row) : Prop :=
  0 ≤ w.left ∧ 0 ≤ w.right ∧ 0 < w.scale ∧
  w.left * a.x + w.right * b.x = w.scale * target.x ∧
  w.left * a.y + w.right * b.y = w.scale * target.y ∧
  w.left * a.constant + w.right * b.constant = w.scale * target.constant ∧
  (target.strict = true →
    (0 < w.left ∧ a.strict = true) ∨ (0 < w.right ∧ b.strict = true))

instance (w : TwoRow) (a b target : Row) : Decidable (w.Check a b target) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem TwoRow.Check.eval_identity {w : TwoRow} {a b target : Row}
    (checked : w.Check a b target) (p : Fin 2 → ℝ) :
    (w.left : ℝ) * a.eval p + (w.right : ℝ) * b.eval p =
      (w.scale : ℝ) * target.eval p := by
  obtain ⟨_, _, _, hx, hy, hc, _⟩ := checked
  have hx' : (w.left : ℝ) * a.x + (w.right : ℝ) * b.x =
      (w.scale : ℝ) * target.x := by exact_mod_cast hx
  have hy' : (w.left : ℝ) * a.y + (w.right : ℝ) * b.y =
      (w.scale : ℝ) * target.y := by exact_mod_cast hy
  have hc' : (w.left : ℝ) * a.constant + (w.right : ℝ) * b.constant =
      (w.scale : ℝ) * target.constant := by exact_mod_cast hc
  calc
    (w.left : ℝ) * a.eval p + (w.right : ℝ) * b.eval p =
        ((w.left : ℝ) * a.x + (w.right : ℝ) * b.x) * p 0 +
        ((w.left : ℝ) * a.y + (w.right : ℝ) * b.y) * p 1 +
        ((w.left : ℝ) * a.constant + (w.right : ℝ) * b.constant) := by
          dsimp [Row.eval]
          ring
    _ = (w.scale : ℝ) * target.eval p := by
      rw [hx', hy', hc']
      dsimp [Row.eval]
      ring

theorem TwoRow.Check.sound {w : TwoRow} {a b target : Row}
    (checked : w.Check a b target) (p : Fin 2 → ℝ)
    (ha : a.Holds p) (hb : b.Holds p) : target.Holds p := by
  have identity := checked.eval_identity p
  obtain ⟨hleft, hright, hscale, _, _, _, hstrict⟩ := checked
  have hl : (0 : ℝ) ≤ w.left := by exact_mod_cast hleft
  have hr : (0 : ℝ) ≤ w.right := by exact_mod_cast hright
  have hs : (0 : ℝ) < w.scale := by exact_mod_cast hscale
  have hla := mul_nonneg hl (a.nonneg p ha)
  have hrb := mul_nonneg hr (b.nonneg p hb)
  by_cases ht : target.strict = true
  · have positive : 0 < (w.scale : ℝ) * target.eval p := by
      rw [← identity]
      rcases hstrict ht with h | h
      · have hl' : (0 : ℝ) < w.left := by exact_mod_cast h.1
        exact add_pos_of_pos_of_nonneg (mul_pos hl' (a.positive p h.2 ha)) hrb
      · have hr' : (0 : ℝ) < w.right := by exact_mod_cast h.1
        exact add_pos_of_nonneg_of_pos hla (mul_pos hr' (b.positive p h.2 hb))
    have htarget : 0 < target.eval p :=
      by nlinarith only [positive, hs]
    simpa [Row.Holds, ht] using htarget
  · have nonnegative : 0 ≤ (w.scale : ℝ) * target.eval p := by
      rw [← identity]
      exact add_nonneg hla hrb
    have htarget : 0 ≤ target.eval p :=
      by nlinarith only [nonnegative, hs]
    simpa [Row.Holds, ht] using htarget

/-- Bridge the integer check directly to the unchanged original normalized
enclosure rows. No packing predicate is redefined or assumed here. -/
theorem TwoRow.Check.normalized_sound {w : TwoRow} {a b target : Row}
    (checked : w.Check a b target) (da db dt : Nat)
    (hda : 0 < da) (hdb : 0 < db) (hdt : 0 < dt) (p : Fin 2 → ℝ)
    (ha : (a.normalized da).Holds p) (hb : (b.normalized db).Holds p) :
    (target.normalized dt).Holds p :=
  (target.normalized_holds_iff dt hdt p).mpr
    (checked.sound p ((a.normalized_holds_iff da hda p).mp ha)
      ((b.normalized_holds_iff db hdb p).mp hb))

#print axioms TwoRow.Check.normalized_sound

end N12Compact.IntegerSupport
