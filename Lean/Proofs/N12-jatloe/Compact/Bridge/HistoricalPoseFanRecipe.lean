import Compact.Core.BoundaryFanSyntax
import Compact.Bridge.IndexedCachedPairPlans
import Mathlib.Data.Nat.GCD.Basic

/-! A fan stores an original pose, an optional pruning block and its cyclic
boundary. Its input rows and reference square are derived from the original
dictionary. Materialization emits data only; the ordinary context check and
all geometric pair or common-point checks remain required. -/

set_option Elab.async false

namespace N12Compact.HistoricalPoseFanRecipe
open S12 IntegerSupport ReferenceAxis VertexFanTable IndexedRelaxation

def referenceDenominator (w : AngleEnclosure) : Nat := w.c.den.lcm w.s.den

theorem referenceDenominator_pos (w : AngleEnclosure) :
    0 < referenceDenominator w := Nat.lcm_pos w.c.den_pos w.s.den_pos

private theorem numerator_normalizes (q : ℚ) (d : Nat) (hp : 0 < d)
    (hd : q.den ∣ d) :
    ((q.num * (d / q.den : Nat) : Int) : ℚ) / d = q := by
  have he : q.den * (d / q.den) = d := Nat.mul_div_cancel' hd
  have he' : (q.den : ℚ) * (d / q.den : Nat) = d := by exact_mod_cast he
  have hq : (q.num : ℚ) = q * q.den :=
    (div_eq_iff (by exact_mod_cast q.den_ne_zero)).mp q.num_div_den
  simp only [Int.cast_mul, Int.cast_natCast]
  rw [hq, mul_assoc, he']
  exact mul_div_cancel_right₀ q (by exact_mod_cast hp.ne')

/-- Exact integer encoding, derived from the original rational angle data. -/
def reference (w : AngleEnclosure) : Reference :=
  let d := referenceDenominator w
  ⟨w.c.num * (d / w.c.den : Nat), w.s.num * (d / w.s.den : Nat),
   d, w.inner.num, w.inner.den⟩

theorem reference_valid (w : AngleEnclosure) : (reference w).Valid :=
  ⟨referenceDenominator_pos w, w.inner.den_pos⟩

theorem reference_exact (w : AngleEnclosure) :
    (reference w).value = w.reference 1 := by
  have hc := numerator_normalizes w.c (referenceDenominator w)
    (referenceDenominator_pos w) (Nat.dvd_lcm_left _ _)
  have hs := numerator_normalizes w.s (referenceDenominator w)
    (referenceDenominator_pos w) (Nat.dvd_lcm_right _ _)
  dsimp only [reference, Reference.value, AngleEnclosure.reference]
  rw [hc, hs, w.inner.num_div_den, one_mul]

structure Recipe (r m : Nat) where
  pose : Fin m
  block : Option Nat
  cycle : List (Fin r)

variable {r m a : Nat}

def Recipe.blockInputs (recipe : Recipe r m) (blocks : Nat → List (Fin r)) :
    List (Fin r) :=
  match recipe.block with
  | none => []
  | some i => blocks i

def Recipe.raw (recipe : Recipe r m) (d : Dictionary r m a)
    (blocks : Nat → List (Fin r)) (directions : Array Direction) : RawContext r :=
  BoundaryFan.context d.rows (recipe.blockInputs blocks ++ d.poseRows recipe.pose)
    (reference (d.angles (d.poseAngle recipe.pose)).val) directions recipe.cycle

/-- Checked recipes retain the actual original pose and its entire input list.
No additional geometric assumption is introduced by the compact encoding. -/
def Recipe.certify (recipe : Recipe r m) (d : Dictionary r m a)
    (blocks : Nat → List (Fin r)) (directions : Array Direction)
    (checked : (recipe.raw d blocks directions).Check d.rows) :
    IndexedCachedPairPlans.PoseContext d where
  pose := recipe.pose
  block := recipe.blockInputs blocks
  keyAngle := (d.poseAngle recipe.pose).val
  context := (recipe.raw d blocks directions).certify d.rows checked
  inputs_exact := rfl
  reference_valid := reference_valid (d.angles (d.poseAngle recipe.pose)).val
  reference_exact := reference_exact (d.angles (d.poseAngle recipe.pose)).val

#print axioms reference_exact
#print axioms Recipe.certify
end N12Compact.HistoricalPoseFanRecipe
