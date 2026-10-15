import Compact.Geometry.WallChain
import Completion.Cases.C977.WallChains

/-!
Adapter from original OpenSquare support data to the generic wall-chain cut.

This module isolates the exact four-axis separation premise from the chain
argument. `Compact.Bridge.CongruentSAT` proves that premise from disjointness
of original squares with equal side lengths. The integrated public wrappers
in `Compact.Bridge.C977DisjointChain` therefore take actual disjointness.
Near-axis, common-height, and axial bounds remain explicit case inputs.
-/

namespace N12Compact.C977ChainBridge

open S12 S12Pilot S12Completion.C977

/-- Combined projection radius on a face normal belonging to the first
square. No equality of the two side lengths is assumed in this definition. -/
noncomputable def pairRadius (q r : OpenSquare) : ℝ :=
  q.side / 2 + r.side / 2 * (|normalDot q r| + |normalCross q r|)

/-- The exact weak-contact SAT conclusion required from original-square
disjointness. Four absolute-value alternatives retain both directions. -/
def FaceSeparation (q r : OpenSquare) : Prop :=
  let X := centerX r - centerX q
  let Y := centerY r - centerY q
  pairRadius q r ≤ |q.c * X + q.s * Y| ∨
  pairRadius q r ≤ |-q.s * X + q.c * Y| ∨
  pairRadius r q ≤ |r.c * X + r.s * Y| ∨
  pairRadius r q ≤ |-r.s * X + r.c * Y|

private theorem normalDot_swap (q r : OpenSquare) :
    normalDot r q = normalDot q r := by
  dsimp [normalDot]
  ring

private theorem normalCross_swap (q r : OpenSquare) :
    normalCross r q = -normalCross q r := by
  dsimp [normalCross]
  ring

/-- The forward projection is positive and the transverse projection is
too small to separate side-greater-than-one squares. -/
theorem near_axis_projection_bounds (q : OpenSquare) (hq : NearAxis q)
    (X Y h : ℝ) (hX : 0 ≤ X) (hY : |Y| ≤ h)
    (hforward : 0 < (99 / 100) * X - (1 / 10) * h)
    (htransverse : (1 / 10) * X + h < 1) :
    0 < q.c * X + q.s * Y ∧ |-q.s * X + q.c * Y| < 1 := by
  have hc := near_axis_cos q hq
  have hsY : |q.s * Y| ≤ (1 / 10) * h := by
    rw [abs_mul]
    exact mul_le_mul hq.2 hY (abs_nonneg Y) (by norm_num)
  have hcX := mul_le_mul_of_nonneg_right hc.1 hX
  have hsX := mul_le_mul_of_nonneg_right hq.2 hX
  have hcY : q.c * |Y| ≤ h := by
    have ht := mul_le_mul hc.2 hY (abs_nonneg Y) (show (0 : ℝ) ≤ 1 by norm_num)
    simpa only [one_mul] using ht
  constructor
  · have hneg := neg_le_abs (q.s * Y)
    linarith
  · have ht := abs_add (-q.s * X) (q.c * Y)
    simp only [abs_mul, abs_neg, abs_of_nonneg hX, abs_of_nonneg hq.1] at ht
    linarith

/-- Exact relative support plus the rational normal-variation gain from the
checked helper gives the local inequality used by the summation theorem. -/
theorem pair_step_of_face_separation (q r : OpenSquare) (a h : ℝ)
    (ha : 1 < a) (hqa : q.side = a) (hra : r.side = a)
    (hq : NearAxis q) (hr : NearAxis r)
    (hX : 0 ≤ centerX r - centerX q)
    (hY : |centerY r - centerY q| ≤ h)
    (hforward : 0 < (99 / 100) * (centerX r - centerX q) - (1 / 10) * h)
    (htransverse : (1 / 10) * (centerX r - centerX q) + h < 1)
    (hsat : FaceSeparation q r) :
    ∃ b : ℝ, (b = q.s ∨ b = r.s) ∧
      a + a * (43 / 100) * |r.s - q.s| - b * (centerY r - centerY q) ≤
        centerX r - centerX q := by
  let X := centerX r - centerX q
  let Y := centerY r - centerY q
  let R := a / 2 * (1 + |normalDot q r| + |normalCross q r|)
  have hRq : pairRadius q r = R := by
    dsimp [pairRadius, R]
    rw [hqa, hra]
    ring
  have hRr : pairRadius r q = R := by
    dsimp [pairRadius, R]
    rw [hqa, hra, normalDot_swap q r, normalCross_swap q r, abs_neg]
    ring
  have hdot : 0 ≤ normalDot q r := by
    have hd := (near_axis_relative_bounds q r hq hr).1
    linarith
  have hgain := near_axis_pair_gain q r hq hr
  have hsupport : a + a * (43 / 100) * |r.s - q.s| ≤ R := by
    have hm := mul_nonneg (show 0 ≤ a by linarith)
      (sub_nonneg.mpr hgain)
    dsimp [R]
    rw [abs_of_nonneg hdot]
    nlinarith
  have hR : 1 < R := by
    have hp := mul_nonneg (show 0 ≤ a * (43 / 100) from
      mul_nonneg (by linarith) (by norm_num))
      (abs_nonneg (r.s - q.s))
    linarith
  have hqp := near_axis_projection_bounds q hq X Y h hX hY hforward htransverse
  have hrp := near_axis_projection_bounds r hr X Y h hX hY hforward htransverse
  have hqcX : q.c * X ≤ X := by
    have hh := mul_le_mul_of_nonneg_right (near_axis_cos q hq).2 hX
    simpa only [one_mul] using hh
  have hrcX : r.c * X ≤ X := by
    have hh := mul_le_mul_of_nonneg_right (near_axis_cos r hr).2 hX
    simpa only [one_mul] using hh
  change pairRadius q r ≤ |q.c * X + q.s * Y| ∨
    pairRadius q r ≤ |-q.s * X + q.c * Y| ∨
    pairRadius r q ≤ |r.c * X + r.s * Y| ∨
    pairRadius r q ≤ |-r.s * X + r.c * Y| at hsat
  rw [hRq, hRr] at hsat
  rcases hsat with hsep | hsep | hsep | hsep
  · rw [abs_of_pos hqp.1] at hsep
    refine ⟨q.s, Or.inl rfl, ?_⟩
    change a + a * (43 / 100) * |r.s - q.s| - q.s * Y ≤ X
    calc
      _ ≤ (q.c * X + q.s * Y) - q.s * Y :=
        sub_le_sub_right (hsupport.trans hsep) _
      _ = q.c * X := by ring
      _ ≤ X := hqcX
  · linarith [hqp.2]
  · rw [abs_of_pos hrp.1] at hsep
    refine ⟨r.s, Or.inr rfl, ?_⟩
    change a + a * (43 / 100) * |r.s - q.s| - r.s * Y ≤ X
    calc
      _ ≤ (r.c * X + r.s * Y) - r.s * Y :=
        sub_le_sub_right (hsupport.trans hsep) _
      _ = r.c * X := by ring
      _ ≤ X := hrcX
  · linarith [hrp.2]

/-- A chain in the original square model. The endpoint wall inequality is
derived from actual open-square containment, not left as an extra premise. -/
theorem openSquare_chain_cut (n : ℕ) (q : ℕ → OpenSquare) (a lower h : ℝ)
    (ha : 1 < a) (hh : h ≤ 43 / 100)
    (hside : ∀ i, i ≤ n → (q i).side = a)
    (hnormal : ∀ i, i ≤ n → NearAxis (q i))
    (hheight : ∀ i, i ≤ n → lower ≤ centerY (q i) ∧ centerY (q i) ≤ lower + h)
    (hgap : ∀ i, i < n →
      0 ≤ centerX (q (i + 1)) - centerX (q i) ∧
      0 < (99 / 100) * (centerX (q (i + 1)) - centerX (q i)) - (1 / 10) * h ∧
      (1 / 10) * (centerX (q (i + 1)) - centerX (q i)) + h < 1)
    (hsat : ∀ i, i < n → FaceSeparation (q i) (q (i + 1)))
    (hwall : ∀ x y, (q n).Inside x y → 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4) :
    centerX (q 0) < 4 - ((n : ℝ) + 1 / 2) := by
  classical
  have localStep : ∀ i, i < n → ∃ b : ℝ,
      (b = (q i).s ∨ b = (q (i + 1)).s) ∧
      a + a * (43 / 100) * |(q (i + 1)).s - (q i).s| -
        b * (centerY (q (i + 1)) - centerY (q i)) ≤
        centerX (q (i + 1)) - centerX (q i) := by
    intro i hi
    have hi0 : i ≤ n := Nat.le_of_lt hi
    have hi1 : i + 1 ≤ n := hi
    have hY := WallChain.height_distance lower h
      (centerY (q (i + 1))) (centerY (q i))
      (hheight (i + 1) hi1) (hheight i hi0)
    exact pair_step_of_face_separation (q i) (q (i + 1)) a h ha
      (hside i hi0) (hside (i + 1) hi1)
      (hnormal i hi0) (hnormal (i + 1) hi1)
      (hgap i hi).1 hY (hgap i hi).2.1 (hgap i hi).2.2 (hsat i hi)
  let b : ℕ → ℝ := fun i =>
    if hi : i < n then Classical.choose (localStep i hi) else (q i).s
  have hb : ∀ i, i < n →
      (b i = (q i).s ∨ b i = (q (i + 1)).s) ∧
      a + a * (43 / 100) * |(q (i + 1)).s - (q i).s| -
        b i * (centerY (q (i + 1)) - centerY (q i)) ≤
        centerX (q (i + 1)) - centerX (q i) := by
    intro i hi
    dsimp [b]
    rw [dif_pos hi]
    exact Classical.choose_spec (localStep i hi)
  have hend := near_axis_right_wall (q n) (hnormal n (Nat.le_refl _)) hwall
  rw [hside n (Nat.le_refl _)] at hend
  exact WallChain.first_center_cut n (fun i => centerX (q i))
    (fun i => centerY (q i)) (fun i => (q i).s) b a (43 / 100)
    lower h 4 ha (by norm_num) hh (fun i hi => (hb i hi).1)
    hheight (fun i hi => (hb i hi).2) hend

end N12Compact.C977ChainBridge
