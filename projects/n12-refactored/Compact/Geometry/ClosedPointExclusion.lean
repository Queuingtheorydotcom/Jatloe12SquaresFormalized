import Compact.Geometry.FourSquareAnchors
import S12.WallGeometry

/-! Closed compulsory points of a foreign square are excluded by disjoint
open interiors. The proof explicitly approaches the closed point from the
foreign square's center; it does not assume strict ownership at the boundary.
No common side, angle restriction, or containment hypothesis is needed. -/

namespace N12Compact.ClosedPointExclusion

open S12 S12Pilot FourSquareAnchors

/-- Closed membership is preserved along a closed segment, including its
vertices. This supplies the foreign-hull premise used by the original replay. -/
theorem closed_segment (q : OpenSquare) (x₀ y₀ x₁ y₁ t : ℝ)
    (h₀ : ClosedInside q x₀ y₀) (h₁ : ClosedInside q x₁ y₁)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ClosedInside q ((1-t)*x₀+t*x₁) ((1-t)*y₀+t*y₁) := by
  have hc : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [mul_nonneg hc (sub_nonneg.mpr h₀.1),
      mul_nonneg ht (sub_nonneg.mpr h₁.1)]
  · nlinarith only [mul_nonneg hc (sub_nonneg.mpr h₀.2.1),
      mul_nonneg ht (sub_nonneg.mpr h₁.2.1)]
  · nlinarith only [mul_nonneg hc (sub_nonneg.mpr h₀.2.2.1),
      mul_nonneg ht (sub_nonneg.mpr h₁.2.2.1)]
  · nlinarith only [mul_nonneg hc (sub_nonneg.mpr h₀.2.2.2),
      mul_nonneg ht (sub_nonneg.mpr h₁.2.2.2)]

private theorem positive_near_zero (a b : ℝ) (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → 0 < a + b * t := by
  let ε := a / (2 * (|b| + 1))
  have hd : 0 < 2 * (|b| + 1) := by nlinarith [abs_nonneg b]
  refine ⟨ε, div_pos ha hd, ?_⟩
  intro t ht htε
  have hsmall : t * (2 * (|b| + 1)) < a := (lt_div_iff₀ hd).mp htε
  have hbound : -|b| * t ≤ b * t :=
    mul_le_mul_of_nonneg_right (neg_abs_le b) ht.le
  nlinarith

private theorem convex_strict (l u p m t : ℝ)
    (hp : l ≤ p ∧ p ≤ u) (hm : l < m ∧ m < u)
    (ht : 0 < t) (ht1 : t < 1) :
    l < (1 - t) * p + t * m ∧ (1 - t) * p + t * m < u := by
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ 1 - t by linarith) (sub_nonneg.mpr hp.1),
      mul_pos ht (sub_pos.mpr hm.1)]
  · nlinarith [mul_nonneg (show 0 ≤ 1 - t by linarith) (sub_nonneg.mpr hp.2),
      mul_pos ht (sub_pos.mpr hm.2)]

/-- A point on a foreign face or vertex still cannot be strictly inside a
square whose open interior is disjoint from that foreign square. -/
theorem outside_of_closed (q r : OpenSquare) (x y : ℝ)
    (apart : ∀ x y, ¬ (q.Inside x y ∧ r.Inside x y))
    (foreign : ClosedInside r x y) : ¬ q.Inside x y := by
  intro own
  let du := q.c * (centerX r - x) + q.s * (centerY r - y)
  let dv := -q.s * (centerX r - x) + q.c * (centerY r - y)
  obtain ⟨e₀, he₀, h₀⟩ := positive_near_zero
    (q.c * x + q.s * y - q.loU) du (by linarith [own.1])
  obtain ⟨e₁, he₁, h₁⟩ := positive_near_zero
    (q.loU + q.side - (q.c * x + q.s * y)) (-du) (by linarith [own.2.1])
  obtain ⟨e₂, he₂, h₂⟩ := positive_near_zero
    (-q.s * x + q.c * y - q.loV) dv (by linarith [own.2.2.1])
  obtain ⟨e₃, he₃, h₃⟩ := positive_near_zero
    (q.loV + q.side - (-q.s * x + q.c * y)) (-dv) (by linarith [own.2.2.2])
  let e := min e₀ (min e₁ (min e₂ (min e₃ 1)))
  have he : 0 < e := lt_min he₀ (lt_min he₁ (lt_min he₂ (lt_min he₃ (by norm_num))))
  let t := e / 2
  have ht : 0 < t := by dsimp [t]; linarith only [he]
  have hte : t < e := by dsimp [t]; linarith only [he]
  have et₀ : e ≤ e₀ := min_le_left _ _
  have et₁ : e ≤ e₁ := (min_le_right _ _).trans (min_le_left _ _)
  have et₂ : e ≤ e₂ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have et₃ : e ≤ e₃ := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have et₄ : e ≤ 1 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have ht1 : t < 1 := hte.trans_le et₄
  let X := (1 - t) * x + t * centerX r
  let Y := (1 - t) * y + t * centerY r
  have qu : q.c * X + q.s * Y = q.c * x + q.s * y + du * t := by
    dsimp [X, Y, du]; ring
  have qv : -q.s * X + q.c * Y = -q.s * x + q.c * y + dv * t := by
    dsimp [X, Y, dv]; ring
  have iq : q.Inside X Y := by
    dsimp [OpenSquare.Inside, InBands]
    rw [qu, qv]
    exact ⟨by linarith [h₀ t ht (hte.trans_le et₀)],
      by linarith [h₁ t ht (hte.trans_le et₁)],
      by linarith [h₂ t ht (hte.trans_le et₂)],
      by linarith [h₃ t ht (hte.trans_le et₃)]⟩
  have ru : r.c * X + r.s * Y =
      (1 - t) * (r.c * x + r.s * y) + t * (r.loU + r.side / 2) := by
    calc
      _ = (1 - t) * (r.c * x + r.s * y) +
          t * (r.c * centerX r + r.s * centerY r) := by dsimp [X, Y]; ring
      _ = _ := by rw [(center_coordinates r).1]
  have rv : -r.s * X + r.c * Y =
      (1 - t) * (-r.s * x + r.c * y) + t * (r.loV + r.side / 2) := by
    calc
      _ = (1 - t) * (-r.s * x + r.c * y) +
          t * (-r.s * centerX r + r.c * centerY r) := by dsimp [X, Y]; ring
      _ = _ := by rw [(center_coordinates r).2]
  have iu := convex_strict r.loU (r.loU + r.side) _ (r.loU + r.side / 2) t
    ⟨foreign.1, foreign.2.1⟩ ⟨by linarith [r.side_pos], by linarith [r.side_pos]⟩ ht ht1
  have iv := convex_strict r.loV (r.loV + r.side) _ (r.loV + r.side / 2) t
    ⟨foreign.2.2.1, foreign.2.2.2⟩ ⟨by linarith [r.side_pos], by linarith [r.side_pos]⟩ ht ht1
  have ir : r.Inside X Y := by
    dsimp [OpenSquare.Inside, InBands]
    rw [ru, rv]
    exact ⟨iu.1, iu.2, iv.1, iv.2⟩
  exact apart X Y ⟨iq, ir⟩

end N12Compact.ClosedPointExclusion
