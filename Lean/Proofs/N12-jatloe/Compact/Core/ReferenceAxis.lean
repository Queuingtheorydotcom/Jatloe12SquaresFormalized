import Compact.Core.PairSupport
import S12.AxisOverlapCertificate

/-!
Exact integer construction of the eight original separating-axis targets.
Only the final bridge uses rational arithmetic. Certificate evaluation uses
integer products and absolute values, with positive denominators explicit.
-/

namespace N12Compact.ReferenceAxis

open S12 PairSupport

structure Reference where
  c : Int
  s : Int
  denominator : Nat
  side : Int
  sideDenominator : Nat
  deriving DecidableEq

def Reference.value (r : Reference) : ReferenceSquare :=
  ⟨(r.c : ℚ) / r.denominator, (r.s : ℚ) / r.denominator,
    (r.side : ℚ) / r.sideDenominator⟩

def Reference.Valid (r : Reference) : Prop :=
  0 < r.denominator ∧ 0 < r.sideDenominator

instance (r : Reference) : Decidable r.Valid :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Direction where
  x : Int
  y : Int
  denominator : Nat
  deriving DecidableEq

def Direction.xq (n : Direction) : ℚ := (n.x : ℚ) / n.denominator
def Direction.yq (n : Direction) : ℚ := (n.y : ℚ) / n.denominator

def radiusNumerator (r : Reference) (n : Direction) : Int :=
  r.side * (|n.x * r.c + n.y * r.s| + |-n.x * r.s + n.y * r.c|)

def radiusDenominator (r : Reference) (n : Direction) : Nat :=
  2 * n.denominator * r.denominator * r.sideDenominator

theorem radius_exact (r : Reference) (n : Direction) (hr : r.Valid)
    (hn : 0 < n.denominator) :
    r.value.ratRadius n.xq n.yq =
      (radiusNumerator r n : ℚ) / radiusDenominator r n := by
  have hd : (r.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr.1
  have hs : (r.sideDenominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr.2
  have hn' : (n.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hp : (0 : ℚ) < (n.denominator : ℚ) * r.denominator := by
    exact mul_pos (by exact_mod_cast hn) (by exact_mod_cast hr.1)
  have dot : n.xq * r.value.c + n.yq * r.value.s =
      ((n.x * r.c + n.y * r.s : Int) : ℚ) /
        ((n.denominator : ℚ) * r.denominator) := by
    dsimp [Direction.xq, Direction.yq, Reference.value]
    push_cast
    field_simp
  have cross : -n.xq * r.value.s + n.yq * r.value.c =
      ((-n.x * r.s + n.y * r.c : Int) : ℚ) /
        ((n.denominator : ℚ) * r.denominator) := by
    dsimp [Direction.xq, Direction.yq, Reference.value]
    push_cast
    field_simp
    <;> ring
  unfold ReferenceSquare.ratRadius
  rw [dot, cross, abs_div, abs_div, abs_of_pos hp]
  simp only [← Int.cast_abs]
  dsimp [Reference.value, radiusNumerator, radiusDenominator]
  push_cast
  field_simp
  <;> ring <;> simp

def targetDenominator (a b : Reference) (n : Direction) : Nat :=
  2 * n.denominator * a.denominator * a.sideDenominator *
    b.denominator * b.sideDenominator

def target (a b : Reference) (n : Direction) : Target :=
  ⟨n.x * 2 * a.denominator * a.sideDenominator * b.denominator * b.sideDenominator,
    n.y * 2 * a.denominator * a.sideDenominator * b.denominator * b.sideDenominator,
    radiusNumerator a n * b.denominator * b.sideDenominator +
      radiusNumerator b n * a.denominator * a.sideDenominator⟩

theorem targetDenominator_positive (a b : Reference) (n : Direction)
    (ha : a.Valid) (hb : b.Valid) (hn : 0 < n.denominator) :
    0 < targetDenominator a b n := by
  unfold targetDenominator
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  positivity

/-- The computed integer target is exactly the original strict axis row,
not merely an approximation to it. -/
theorem target_exact (a b : Reference) (n : Direction)
    (ha : a.Valid) (hb : b.Valid) (hn : 0 < n.denominator) :
    (target a b n).normalized (targetDenominator a b n) =
      axisGapForm a.value b.value n.xq n.yq := by
  have ha₁ : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha.1
  have ha₂ : (a.sideDenominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha.2
  have hb₁ : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb.1
  have hb₂ : (b.sideDenominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb.2
  have hn' : (n.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hx : ((target a b n).x : ℚ) / targetDenominator a b n = n.xq := by
    dsimp [target, targetDenominator, Direction.xq]
    push_cast
    field_simp
    <;> ring
  have hy : ((target a b n).y : ℚ) / targetDenominator a b n = n.yq := by
    dsimp [target, targetDenominator, Direction.yq]
    push_cast
    field_simp
    <;> ring
  have hc : ((target a b n).constant : ℚ) / targetDenominator a b n =
      a.value.ratRadius n.xq n.yq + b.value.ratRadius n.xq n.yq := by
    rw [radius_exact a n ha hn, radius_exact b n hb hn]
    dsimp [target, targetDenominator, radiusDenominator]
    push_cast
    field_simp
    <;> ring
  simp only [Target.normalized, axisGapForm, neg_div, hx, hy, hc]

def directions (a b : Reference) : List Direction :=
  [⟨a.c, a.s, a.denominator⟩, ⟨-a.c, -a.s, a.denominator⟩,
    ⟨-a.s, a.c, a.denominator⟩, ⟨a.s, -a.c, a.denominator⟩,
    ⟨b.c, b.s, b.denominator⟩, ⟨-b.c, -b.s, b.denominator⟩,
    ⟨-b.s, b.c, b.denominator⟩, ⟨b.s, -b.c, b.denominator⟩]

theorem directions_positive (a b : Reference) (ha : a.Valid) (hb : b.Valid)
    (n : Direction) (hn : n ∈ directions a b) : 0 < n.denominator := by
  simp only [directions, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ha.1 | exact hb.1

theorem targets_exact (a b : Reference) (ha : a.Valid) (hb : b.Valid) :
    (directions a b).map (fun n =>
      (target a b n).normalized (targetDenominator a b n)) =
      axisOverlapForms a.value b.value := by
  calc
    _ = (directions a b).map (fun n => axisGapForm a.value b.value n.xq n.yq) := by
      apply List.map_congr_left
      intro n hn
      exact target_exact a b n ha hb (directions_positive a b ha hb n hn)
    _ = _ := by
      simp [directions, axisOverlapForms, pairAxes, Direction.xq, Direction.yq,
        Reference.value, neg_div]

theorem overlap (a b : Reference) (ha : a.Valid) (hb : b.Valid)
    (hac : a.value.Check) (hbc : b.value.Check) (p q : Fin 2 → ℝ)
    (checks : ∀ n ∈ directions a b, 0 < (target a b n).eval p q) :
    OverlapsAt (a.value.toSquare hac) (b.value.toSquare hbc)
      (p 0, p 1) (q 0, q 1) := by
  apply axisOverlapForms_sound a.value b.value hac hbc ![p 0, p 1, q 0, q 1]
  intro row hrow
  rw [← targets_exact a b ha hb] at hrow
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hrow
  apply ((target a b n).normalized_holds_iff (targetDenominator a b n)
    (targetDenominator_positive a b n ha hb (directions_positive a b ha hb n hn)) p q).mpr
  exact checks n hn

#print axioms overlap

end N12Compact.ReferenceAxis
