import S12.Diagonal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Strict anchors from the CLOSED point premises of the shared four-square
template. Noncollinearity prevents three closed points from lying on any
one face, so their centroid is strict in both face coordinates.

This is a symbolic premise upgrade for the original OpenSquare model. It
does not assert the unproved five pair-pruning steps or long-section bounds.
-/

namespace N12Compact.FourSquareAnchors

open S12Pilot

def ClosedInside (q : OpenSquare) (x y : ℝ) : Prop :=
  q.loU ≤ q.c * x + q.s * y ∧ q.c * x + q.s * y ≤ q.loU + q.side ∧
  q.loV ≤ -q.s * x + q.c * y ∧ -q.s * x + q.c * y ≤ q.loV + q.side

def determinant (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) : ℝ :=
  (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀)

private theorem nonconstant_projection (A B x₀ y₀ x₁ y₁ x₂ y₂ : ℝ)
    (hunit : A ^ 2 + B ^ 2 = 1)
    (hdet : determinant x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    ¬ (A * x₀ + B * y₀ = A * x₁ + B * y₁ ∧
       A * x₀ + B * y₀ = A * x₂ + B * y₂) := by
  intro he
  have h₁ : A * (x₁ - x₀) + B * (y₁ - y₀) = 0 := by linarith [he.1]
  have h₂ : A * (x₂ - x₀) + B * (y₂ - y₀) = 0 := by linarith [he.2]
  have hA : A * determinant x₀ y₀ x₁ y₁ x₂ y₂ = 0 := by
    calc
      _ = (A * (x₁ - x₀) + B * (y₁ - y₀)) * (y₂ - y₀) -
          (A * (x₂ - x₀) + B * (y₂ - y₀)) * (y₁ - y₀) := by
            unfold determinant
            ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hB : B * determinant x₀ y₀ x₁ y₁ x₂ y₂ = 0 := by
    calc
      _ = (x₁ - x₀) * (A * (x₂ - x₀) + B * (y₂ - y₀)) -
          (x₂ - x₀) * (A * (x₁ - x₀) + B * (y₁ - y₀)) := by
            unfold determinant
            ring
      _ = 0 := by rw [h₁, h₂]; ring
  have hA₀ := (mul_eq_zero.mp hA).resolve_right hdet
  have hB₀ := (mul_eq_zero.mp hB).resolve_right hdet
  nlinarith

private theorem strict_mean (l u a b c : ℝ)
    (ha : l ≤ a ∧ a ≤ u) (hb : l ≤ b ∧ b ≤ u) (hc : l ≤ c ∧ c ≤ u)
    (hne : ¬ (a = b ∧ a = c)) :
    l < (a + b + c) / 3 ∧ (a + b + c) / 3 < u := by
  constructor
  · by_contra hh
    have hm : (a + b + c) / 3 ≤ l := le_of_not_gt hh
    have ha₀ : a = l := by linarith [ha.1, hb.1, hc.1]
    have hb₀ : b = l := by linarith [ha.1, hb.1, hc.1]
    have hc₀ : c = l := by linarith [ha.1, hb.1, hc.1]
    exact hne ⟨ha₀.trans hb₀.symm, ha₀.trans hc₀.symm⟩
  · by_contra hh
    have hm : u ≤ (a + b + c) / 3 := le_of_not_gt hh
    have ha₀ : a = u := by linarith [ha.2, hb.2, hc.2]
    have hb₀ : b = u := by linarith [ha.2, hb.2, hc.2]
    have hc₀ : c = u := by linarith [ha.2, hb.2, hc.2]
    exact hne ⟨ha₀.trans hb₀.symm, ha₀.trans hc₀.symm⟩

/-- Closed membership of a nondegenerate triangle forces strict membership
of its centroid, including when the required vertices touch square faces. -/
theorem centroid_inside (q : OpenSquare) (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ)
    (h₀ : ClosedInside q x₀ y₀) (h₁ : ClosedInside q x₁ y₁)
    (h₂ : ClosedInside q x₂ y₂)
    (hdet : determinant x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    q.Inside ((x₀ + x₁ + x₂) / 3) ((y₀ + y₁ + y₂) / 3) := by
  have hu := strict_mean q.loU (q.loU + q.side)
    (q.c * x₀ + q.s * y₀) (q.c * x₁ + q.s * y₁) (q.c * x₂ + q.s * y₂)
    ⟨h₀.1, h₀.2.1⟩ ⟨h₁.1, h₁.2.1⟩ ⟨h₂.1, h₂.2.1⟩
    (nonconstant_projection q.c q.s x₀ y₀ x₁ y₁ x₂ y₂ q.unit_normal hdet)
  have hv := strict_mean q.loV (q.loV + q.side)
    (-q.s * x₀ + q.c * y₀) (-q.s * x₁ + q.c * y₁) (-q.s * x₂ + q.c * y₂)
    ⟨h₀.2.2.1, h₀.2.2.2⟩ ⟨h₁.2.2.1, h₁.2.2.2⟩ ⟨h₂.2.2.1, h₂.2.2.2⟩
    (nonconstant_projection (-q.s) q.c x₀ y₀ x₁ y₁ x₂ y₂
      (by nlinarith [q.unit_normal]) hdet)
  change InBands q.loU q.loV q.side _ _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hu.1, hu.2, hv.1, hv.2]

theorem anchor_A (q : OpenSquare)
    (h₀ : ClosedInside q 2 (113 / 50))
    (h₁ : ClosedInside q (113 / 50) 2)
    (h₂ : ClosedInside q (47 / 20) (47 / 20)) :
    q.Inside (661 / 300) (661 / 300) := by
  have hh := centroid_inside q 2 (113 / 50) (113 / 50) 2 (47 / 20) (47 / 20)
    h₀ h₁ h₂ (by norm_num [determinant])
  convert hh using 1 <;> norm_num

theorem anchor_B (q : OpenSquare)
    (h₀ : ClosedInside q (8 / 5) 3)
    (h₁ : ClosedInside q (33 / 20) (47 / 20))
    (h₂ : ClosedInside q (87 / 50) 3) :
    q.Inside (499 / 300) (167 / 60) := by
  have hh := centroid_inside q (8 / 5) 3 (33 / 20) (47 / 20) (87 / 50) 3
    h₀ h₁ h₂ (by norm_num [determinant])
  convert hh using 1 <;> norm_num

theorem anchor_L (q : OpenSquare)
    (h₀ : ClosedInside q (457 / 500) 2)
    (h₁ : ClosedInside q 1 (113 / 50))
    (h₂ : ClosedInside q 1 (12 / 5)) :
    q.Inside (1457 / 1500) (111 / 50) := by
  have hh := centroid_inside q (457 / 500) 2 1 (113 / 50) 1 (12 / 5)
    h₀ h₁ h₂ (by norm_num [determinant])
  convert hh using 1 <;> norm_num

theorem anchor_R (q : OpenSquare)
    (h₀ : ClosedInside q 3 (113 / 50))
    (h₁ : ClosedInside q (1543 / 500) 2)
    (h₂ : ClosedInside q 3 (12 / 5)) :
    q.Inside (4543 / 1500) (111 / 50) := by
  have hh := centroid_inside q 3 (113 / 50) (1543 / 500) 2 3 (12 / 5)
    h₀ h₁ h₂ (by norm_num [determinant])
  convert hh using 1 <;> norm_num

end N12Compact.FourSquareAnchors
