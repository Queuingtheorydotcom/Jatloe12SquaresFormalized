import S12.WallGeometry
import Completion.Cases.C696.SideSignAlgebra

/-!
C696 side-owner sign, in the repository's original arbitrary-rotation OpenSquare
model. No discrete orientation, side upper bound, auxiliary uniqueness, or
missing-corner premise is part of this local theorem.
-/

namespace S12
open S12Pilot
set_option maxHeartbeats 0

private theorem side_owner_sign_positive_frame (q : OpenSquare)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s) (ha : 1 < q.side)
    (hwall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (hA : q.Inside (457/500) 2) (hC : q.Inside 1 (12/5))
    (hD : ¬ q.Inside 1 (87/50)) (hE : ¬ q.Inside (87/50) 2) :
    2 < centerY q := by
  by_contra hheight
  have hY : centerY q ≤ 2 := le_of_not_gt hheight
  have hunit := q.unit_normal
  have hc1 : q.c ≤ 1 := by nlinarith [sq_nonneg q.s]
  have hs1 : q.s ≤ 1 := by nlinarith [sq_nonneg q.c]
  have hsum : 0 < q.c + q.s := by
    by_contra hn
    have hn' : q.c + q.s ≤ 0 := le_of_not_gt hn
    have hc0 : q.c = 0 := by linarith
    have hs0 : q.s = 0 := by linarith
    simp only [hc0, hs0] at hunit
    norm_num at hunit
  have hX := (positive_frame_wall_bounds q hc hs hwall).1
  obtain ⟨hcenterU, hcenterV⟩ := center_coordinates q
  have hcy : 0 ≤ q.c * (2 - centerY q) := mul_nonneg hc (by linarith)
  have hsy : 0 ≤ q.s * (2 - centerY q) := mul_nonneg hs (by linarith)
  have hcx : 0 ≤ q.s * (centerX q - q.side * (q.c + q.s) / 2) :=
    mul_nonneg hs (by linarith)
  rcases hA with ⟨hA0, hA1, hA2, hA3⟩
  rcases hC with ⟨hC0, hC1, hC2, hC3⟩
  have hDcases : q.c * 1 + q.s * (87/50) ≤ q.loU ∨
      -q.s * 1 + q.c * (87/50) ≤ q.loV := by
    simp only [OpenSquare.Inside, InBands, not_and_or, not_lt] at hD
    rcases hD with hd | hd | hd | hd
    · exact Or.inl hd
    · exfalso; linarith
    · exact Or.inr hd
    · exfalso; linarith
  have hEcases : q.loU + q.side ≤ q.c * (87/50) + q.s * 2 ∨
      -q.s * (87/50) + q.c * 2 ≤ q.loV := by
    simp only [OpenSquare.Inside, InBands, not_and_or, not_lt] at hE
    rcases hE with he | he | he | he
    · exfalso; linarith
    · exact Or.inl he
    · exact Or.inr he
    · exfalso; linarith
  rcases hDcases with hlowU | hlowV
  · rcases hEcases with huppU | hElowV
    · -- Opposite faces: the projection difference is bounded by one.
      linarith
    · -- Adjacent lower faces: eliminate the center abscissa exactly.
      have hDbound : q.side/2 ≤ q.c * (centerX q - 1) + (13/50)*q.s := by
        nlinarith
      have hEbound : q.side/2 ≤ q.s * ((87/50) - centerX q) := by
        nlinarith
      have hDweighted := mul_le_mul_of_nonneg_left hDbound hs
      have hEweighted := mul_le_mul_of_nonneg_left hEbound hc
      have hstrict := C696SideSign.adjacent_strict_of_sum_pos q.side q.c q.s
        ha hc hc1 hs hs1 hsum
      nlinarith
  · -- A downward face with nonnegative horizontal component is blocked by
    -- the left wall and the assumed center-height bound.
    have hDbound : q.side/2 ≤ q.s * (1 - centerX q) + (13/50)*q.c := by
      nlinarith
    have hstrict := C696SideSign.positive_horizontal_strict q.side q.s q.c
      ha hs hs1 hc hc1
    nlinarith

/-- An arbitrary square in the container's first quadrant, owning the left
side marker and the upper auxiliary endpoint but excluding the lower and inner
auxiliary points, must have its center strictly above height two. -/
theorem c696_left_side_center_gt_two (q : OpenSquare) (ha : 1 < q.side)
    (hwall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (hA : q.Inside (457/500) 2) (hC : q.Inside 1 (12/5))
    (hD : ¬ q.Inside 1 (87/50)) (hE : ¬ q.Inside (87/50) 2) :
    2 < centerY q := by
  obtain ⟨r, hc, hs, hside, hX, hY, hInside⟩ := exists_positive_frame q
  have ha' : 1 < r.side := by rw [hside]; exact ha
  have hwall' : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hi
    exact hwall x y ((hInside x y).mp hi)
  have hA' := (hInside (457/500) 2).mpr hA
  have hC' := (hInside 1 (12/5)).mpr hC
  have hD' : ¬ r.Inside 1 (87/50) := by
    intro hi; exact hD ((hInside 1 (87/50)).mp hi)
  have hE' : ¬ r.Inside (87/50) 2 := by
    intro hi; exact hE ((hInside (87/50) 2).mp hi)
  rw [← hY]
  exact side_owner_sign_positive_frame r hc hs ha' hwall' hA' hC' hD' hE'

/-- Transposition of the square as a planar set, rather than just a change
of face indexing. -/
private noncomputable def transposeSideSquare (q : OpenSquare) : OpenSquare where
  c := q.s
  s := q.c
  loU := q.loU
  loV := -q.loV - q.side
  side := q.side
  unit_normal := by nlinarith [q.unit_normal]
  side_pos := q.side_pos

private theorem transposeSideSquare_inside (q : OpenSquare) (x y : ℝ) :
    (transposeSideSquare q).Inside x y ↔ q.Inside y x := by
  dsimp [transposeSideSquare, OpenSquare.Inside, InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

private theorem transposeSideSquare_centerY (q : OpenSquare) :
    centerY (transposeSideSquare q) = centerX q := by
  dsimp [transposeSideSquare, centerX, centerY]
  ring

/-- The transposed local statement for the bottom side owner. -/
theorem c696_bottom_side_center_gt_two (q : OpenSquare) (ha : 1 < q.side)
    (hwall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (hA : q.Inside 2 (457/500)) (hC : q.Inside (12/5) 1)
    (hD : ¬ q.Inside (87/50) 1) (hE : ¬ q.Inside 2 (87/50)) :
    2 < centerX q := by
  let r := transposeSideSquare q
  have hi (x y : ℝ) : r.Inside x y ↔ q.Inside y x :=
    transposeSideSquare_inside q x y
  have hwall' : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y h
    have hh := hwall y x ((hi x y).mp h)
    exact ⟨hh.2,hh.1⟩
  have ha' : 1 < r.side := ha
  have hD' : ¬ r.Inside 1 (87/50) := by
    intro h; exact hD ((hi 1 (87/50)).mp h)
  have hE' : ¬ r.Inside (87/50) 2 := by
    intro h; exact hE ((hi (87/50) 2).mp h)
  have h := c696_left_side_center_gt_two r ha' hwall'
    ((hi (457/500) 2).mpr hA) ((hi 1 (12/5)).mpr hC) hD' hE'
  simpa only [r, transposeSideSquare_centerY] using h

/-- Half turn about the center of the side-four container. -/
private noncomputable def halfTurnSideSquare (q : OpenSquare) : OpenSquare where
  c := q.c
  s := q.s
  loU := 4 * (q.c + q.s) - q.loU - q.side
  loV := 4 * (q.c - q.s) - q.loV - q.side
  side := q.side
  unit_normal := q.unit_normal
  side_pos := q.side_pos

private theorem halfTurnSideSquare_inside (q : OpenSquare) (x y : ℝ) :
    (halfTurnSideSquare q).Inside x y ↔ q.Inside (4-x) (4-y) := by
  dsimp [halfTurnSideSquare, OpenSquare.Inside, InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

private theorem halfTurnSideSquare_centerY (q : OpenSquare) :
    centerY (halfTurnSideSquare q) = 4 - centerY q := by
  dsimp [halfTurnSideSquare, centerY]
  nlinarith [q.unit_normal]

private theorem halfTurnSideSquare_centerX (q : OpenSquare) :
    centerX (halfTurnSideSquare q) = 4 - centerX q := by
  dsimp [halfTurnSideSquare, centerX]
  nlinarith [q.unit_normal]

/-- The rotated local statement for the right side owner. -/
theorem c696_right_side_center_lt_two (q : OpenSquare) (ha : 1 < q.side)
    (hwall : ∀ x y, q.Inside x y → x ≤ 4 ∧ y ≤ 4)
    (hA : q.Inside (1543/500) 2) (hC : q.Inside 3 (8/5))
    (hD : ¬ q.Inside 3 (113/50)) (hE : ¬ q.Inside (113/50) 2) :
    centerY q < 2 := by
  let r := halfTurnSideSquare q
  have hi (x y : ℝ) : r.Inside x y ↔ q.Inside (4-x) (4-y) :=
    halfTurnSideSquare_inside q x y
  have hwall' : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y h
    have hh := hwall (4-x) (4-y) ((hi x y).mp h)
    constructor <;> linarith
  have ha' : 1 < r.side := ha
  have hA' : r.Inside (457/500) 2 := by
    apply (hi (457/500) 2).mpr
    norm_num
    exact hA
  have hC' : r.Inside 1 (12/5) := by
    apply (hi 1 (12/5)).mpr
    norm_num
    exact hC
  have hD' : ¬ r.Inside 1 (87/50) := by
    intro h
    have hh := (hi 1 (87/50)).mp h
    norm_num at hh
    exact hD hh
  have hE' : ¬ r.Inside (87/50) 2 := by
    intro h
    have hh := (hi (87/50) 2).mp h
    norm_num at hh
    exact hE hh
  have h := c696_left_side_center_gt_two r ha' hwall' hA' hC' hD' hE'
  have hcent : centerY r = 4 - centerY q := halfTurnSideSquare_centerY q
  linarith

/-- The transposed rotated local statement for the top side owner. -/
theorem c696_top_side_center_lt_two (q : OpenSquare) (ha : 1 < q.side)
    (hwall : ∀ x y, q.Inside x y → x ≤ 4 ∧ y ≤ 4)
    (hA : q.Inside 2 (1543/500)) (hC : q.Inside (8/5) 3)
    (hD : ¬ q.Inside (113/50) 3) (hE : ¬ q.Inside 2 (113/50)) :
    centerX q < 2 := by
  let r := halfTurnSideSquare q
  have hi (x y : ℝ) : r.Inside x y ↔ q.Inside (4-x) (4-y) :=
    halfTurnSideSquare_inside q x y
  have hwall' : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y h
    have hh := hwall (4-x) (4-y) ((hi x y).mp h)
    constructor <;> linarith
  have ha' : 1 < r.side := ha
  have hA' : r.Inside 2 (457/500) := by
    apply (hi 2 (457/500)).mpr
    norm_num
    exact hA
  have hC' : r.Inside (12/5) 1 := by
    apply (hi (12/5) 1).mpr
    norm_num
    exact hC
  have hD' : ¬ r.Inside (87/50) 1 := by
    intro h
    have hh := (hi (87/50) 1).mp h
    norm_num at hh
    exact hD hh
  have hE' : ¬ r.Inside 2 (87/50) := by
    intro h
    have hh := (hi 2 (87/50)).mp h
    norm_num at hh
    exact hE hh
  have h := c696_bottom_side_center_gt_two r ha' hwall' hA' hC' hD' hE'
  have hcent : centerX r = 4 - centerX q := halfTurnSideSquare_centerX q
  linarith

#print axioms c696_left_side_center_gt_two
#print axioms c696_bottom_side_center_gt_two
#print axioms c696_right_side_center_lt_two
#print axioms c696_top_side_center_lt_two
end S12
