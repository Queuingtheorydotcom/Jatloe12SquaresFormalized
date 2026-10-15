import S12.WallGeometry
import S12.SymmetryBase

namespace S12Completion.C977
open S12 S12Pilot
set_option maxHeartbeats 1000000

/-- A signed near-horizontal face frame. Quarter turns change only the
face names; the enclosed original square and its center are preserved. -/
def NearAxis (q : OpenSquare) : Prop := 0 ≤ q.c ∧ |q.s| ≤ 1 / 10

/-- Component bounds needed by the rational wall-chain support estimate. -/
theorem near_axis_cos (q : OpenSquare) (h : NearAxis q) :
    99 / 100 ≤ q.c ∧ q.c ≤ 1 := by
  have hs := abs_le.mp h.2
  have hs2 : q.s^2 ≤ (1 / 10 : ℝ)^2 := by nlinarith [sq_nonneg q.s]
  constructor
  · nlinarith [q.unit_normal, h.1]
  · nlinarith [q.unit_normal, sq_nonneg q.s, sq_nonneg (q.c-1)]

/-- The support at a vertical container wall pays for endpoint normal
variation with the same rational coefficient as the pair estimate. -/
theorem near_axis_wall_gain (q : OpenSquare) (h : NearAxis q) :
    1 + (43 / 50) * |q.s| ≤ q.c + |q.s| := by
  have hc := near_axis_cos q h
  have hb0 := abs_nonneg q.s
  have hb1 := h.2
  have hb2 : |q.s|^2 = q.s^2 := sq_abs q.s
  have hprod := mul_nonneg (show 0 ≤ |q.s| by exact hb0)
    (show 0 ≤ 1 / 10 - |q.s| by linarith)
  by_contra hh
  have hneg : q.c < 1-(7 / 50)*|q.s| := by linarith
  have hfac : 0 < 1-(7 / 50)*|q.s|+q.c := by linarith
  have hsq := mul_pos (show 0 < 1-(7 / 50)*|q.s|-q.c by linarith) hfac
  nlinarith [q.unit_normal]

/-- Absolute cross and dot products of two unit normals. -/
noncomputable def normalDot (q r : OpenSquare) : ℝ := q.c*r.c+q.s*r.s
noncomputable def normalCross (q r : OpenSquare) : ℝ := q.c*r.s-q.s*r.c

/-- This is a polynomial identity, independent of an angle parametrization. -/
theorem normal_pair_unit (q r : OpenSquare) :
    normalDot q r ^ 2 + normalCross q r ^ 2 = 1 := by
  calc
    _ = (q.c^2+q.s^2)*(r.c^2+r.s^2) := by dsimp [normalDot, normalCross]; ring
    _ = 1 := by rw [q.unit_normal, r.unit_normal]; norm_num

/-- A closed rational enclosure for the relative normal. -/
theorem near_axis_relative_bounds (q r : OpenSquare) (hq : NearAxis q) (hr : NearAxis r) :
    97 / 100 ≤ normalDot q r ∧ normalDot q r ≤ 1 ∧ |normalCross q r| ≤ 1 / 5 := by
  have hqc := near_axis_cos q hq
  have hrc := near_axis_cos r hr
  have hqs := abs_le.mp hq.2
  have hrs := abs_le.mp hr.2
  have hprod := mul_nonneg (show 0 ≤ q.c-99/100 by linarith)
    (show 0 ≤ r.c-99/100 by linarith)
  have hss := mul_nonneg (show 0 ≤ q.s+1/10 by linarith)
    (show 0 ≤ r.s+1/10 by linarith)
  have hss' := mul_nonneg (show 0 ≤ 1/10-q.s by linarith)
    (show 0 ≤ 1/10-r.s by linarith)
  have hd : 97 / 100 ≤ normalDot q r := by
    dsimp [normalDot]
    have hprodss : -(1/100 : ℝ) ≤ q.s*r.s := by
      by_cases hsign : 0 ≤ q.s
      · have hh := mul_nonneg hsign (show 0 ≤ r.s+1/10 by linarith)
        nlinarith
      · have hh := mul_nonneg (show 0 ≤ -q.s by linarith)
          (show 0 ≤ 1/10-r.s by linarith)
        nlinarith
    nlinarith
  have hdb : normalDot q r ≤ 1 := by
    have hn := normal_pair_unit q r
    nlinarith [sq_nonneg (normalCross q r), sq_nonneg (normalDot q r-1)]
  refine ⟨hd, hdb, ?_⟩
  apply abs_le.mpr
  have hqrs := mul_le_mul_of_nonneg_left (le_abs_self r.s) hq.1
  have hrqs := mul_le_mul_of_nonneg_left (le_abs_self q.s) hr.1
  have hqrs' := mul_le_mul_of_nonneg_left (neg_le_abs r.s) hq.1
  have hrqs' := mul_le_mul_of_nonneg_left (neg_le_abs q.s) hr.1
  have hqcap := mul_le_mul_of_nonneg_left hq.2 hr.1
  have hrcap := mul_le_mul_of_nonneg_left hr.2 hq.1
  have hqcap' : r.c*|q.s| ≤ 1/10 := by nlinarith [hq.2, abs_nonneg q.s]
  have hrcap' : q.c*|r.s| ≤ 1/10 := by nlinarith [hr.2, abs_nonneg r.s]
  dsimp [normalCross]
  constructor <;> nlinarith

/-- Gain in the exact pair support controls the difference of signed
vertical components. This replaces analytic sine Lipschitz estimates. -/
theorem near_axis_pair_gain (q r : OpenSquare) (hq : NearAxis q) (hr : NearAxis r) :
    1 + (43 / 50) * |r.s-q.s| ≤ normalDot q r + |normalCross q r| := by
  have hb := near_axis_relative_bounds q r hq hr
  have hqc := near_axis_cos q hq
  have hrc := near_axis_cos r hr
  have hn := normal_pair_unit q r
  have hc0 := abs_nonneg (normalCross q r)
  have hc2 : |normalCross q r|^2 = normalCross q r^2 := sq_abs _
  have hsup : 1 + (89 / 100)*|normalCross q r| ≤ normalDot q r+|normalCross q r| := by
    by_contra hh
    have hgap : (11 / 100)*|normalCross q r| < 1-normalDot q r := by linarith
    have hpos := mul_pos (show 0 < 1-normalDot q r-(11/100)*|normalCross q r| by linarith)
      (show 0 < 1+normalDot q r by linarith)
    have hcap := mul_nonneg hc0 (show 0 ≤ 1/5-|normalCross q r| by linarith)
    have hlow := mul_nonneg hc0 (show 0 ≤ normalDot q r-97/100 by linarith)
    nlinarith
  have hidentity : normalCross q r*(q.c+r.c) = (r.s-q.s)*(1+normalDot q r) := by
    calc
      _ = r.s*(q.c^2+q.s^2)-q.s*(r.c^2+r.s^2)+(r.s-q.s)*normalDot q r := by
        dsimp [normalCross, normalDot]; ring
      _ = (r.s-q.s)*(1+normalDot q r) := by rw [q.unit_normal, r.unit_normal]; ring
  have habs : |normalCross q r| *(q.c+r.c) = |r.s-q.s| *(1+normalDot q r) := by
    have hh := congrArg abs hidentity
    simpa only [abs_mul, abs_of_nonneg (show 0 ≤ q.c+r.c by linarith [hq.1, hr.1]),
      abs_of_nonneg (show 0 ≤ 1+normalDot q r by linarith)] using hh
  have hdc := mul_nonneg (abs_nonneg (r.s-q.s))
    (show 0 ≤ normalDot q r-97/100 by linarith)
  have hcc := mul_nonneg hc0 (show 0 ≤ 2-(q.c+r.c) by linarith)
  nlinarith

/-- The left-wall support inequality is valid for either sign of the
near-horizontal normal, and is proved from containment of the open set. -/
theorem near_axis_left_wall (q : OpenSquare) (hq : NearAxis q)
    (hw : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y) :
    q.side / 2 + q.side*(43/100)*|q.s| ≤ centerX q := by
  have hsupport : q.side*(q.c+|q.s|)/2 ≤ centerX q := by
    by_cases hs : 0 ≤ q.s
    · simpa only [abs_of_nonneg hs] using (positive_frame_wall_bounds q hq.1 hs hw).1
    · have hh : ∀ x y, (turnFrame q).Inside x y → 0 ≤ x ∧ 0 ≤ y := by
        intro x y hi
        exact hw x y ((turnFrame_inside q x y).mp hi)
      have ht := (positive_frame_wall_bounds (turnFrame q)
        (show 0 ≤ (turnFrame q).c by dsimp [turnFrame]; linarith)
        (show 0 ≤ (turnFrame q).s from hq.1) hh).1
      rw [turnFrame_centerX] at ht
      dsimp [turnFrame] at ht
      simpa only [abs_of_neg (lt_of_not_ge hs), add_comm] using ht
  have hg := near_axis_wall_gain q hq
  have hm := mul_nonneg q.side_pos.le (sub_nonneg.mpr hg)
  nlinarith

/-- Right-wall containment has the same endpoint support budget. -/
theorem near_axis_right_wall (q : OpenSquare) (hq : NearAxis q)
    (hw : ∀ x y, q.Inside x y → 0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4) :
    q.side / 2 + q.side*(43/100)*|q.s| ≤ 4-centerX q := by
  let r := turnFrame (turnFrame (pullX q))
  have hr : NearAxis r := by
    constructor
    · simpa [r, turnFrame, pullX] using hq.1
    · simpa [r, turnFrame, pullX] using hq.2
  have hwall : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
    intro x y hi
    have hqxy : q.Inside (4-x) y := by simpa [r, turnFrame_inside, inside_pullX] using hi
    have hh := hw (4-x) y hqxy
    exact ⟨by linarith [hh.2.1], hh.2.2.1⟩
  have hc : centerX r = 4-centerX q := by
    dsimp [r, turnFrame, pullX, centerX]
    nlinarith [q.unit_normal]
  have hh := near_axis_left_wall r hr hwall
  rw [hc] at hh
  simpa [r, turnFrame, pullX] using hh

end S12Completion.C977
