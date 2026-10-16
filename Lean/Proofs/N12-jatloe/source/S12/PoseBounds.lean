import S12.AngleReference
import S12.MarkerCoverGeometry

namespace S12
open S12Pilot
set_option maxHeartbeats 0

theorem positive_frame_all_walls (q : OpenSquare) (hc : 0≤q.c) (hs : 0≤q.s)
    (hb : InsideContainer q) :
    q.side*(q.c+q.s)/2≤centerX q ∧ centerX q≤4-q.side*(q.c+q.s)/2 ∧
    q.side*(q.c+q.s)/2≤centerY q ∧ centerY q≤4-q.side*(q.c+q.s)/2 := by
  have hlo := positive_frame_wall_bounds q hc hs (fun x y hi => ⟨(hb x y hi).1,(hb x y hi).2.2.1⟩)
  have hx : 0≤4-(q.c*(q.loU+q.side)-q.s*q.loV) := by
    apply affine_endpoint_nonnegative q.side (q.c+q.s) _ q.side_pos
    intro t ht0 ht1
    let u := q.loU+q.side-t
    let v := q.loV+t
    have hi : q.Inside (q.c*u-q.s*v) (q.s*u+q.c*v) := by
      apply (inside_iff_rotated_box q _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    have hh := (hb _ _ hi).2.1
    dsimp [u,v] at hh
    nlinarith only [hh]
  have hy : 0≤4-(q.s*(q.loU+q.side)+q.c*(q.loV+q.side)) := by
    apply affine_endpoint_nonnegative q.side (q.c+q.s) _ q.side_pos
    intro t ht0 ht1
    let u := q.loU+q.side-t
    let v := q.loV+q.side-t
    have hi : q.Inside (q.c*u-q.s*v) (q.s*u+q.c*v) := by
      apply (inside_iff_rotated_box q _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    have hh := (hb _ _ hi).2.2.2
    dsimp [u,v] at hh
    nlinarith only [hh]
  refine ⟨hlo.1,?_,hlo.2,?_⟩ <;> dsimp [centerX,centerY] <;> nlinarith only [hx,hy]

/-- Compulsory points give necessary center halfplanes in the reference
orientation. The entire real angle interval is covered. -/
theorem AngleEnclosure.outer_sound (w : AngleEnclosure) (hw : w.Check)
    (upperSide : ℚ) (q : OpenSquare) (t x y : ℝ)
    (hc : q.c=normalC t) (hs : q.s=normalS t)
    (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ)) (hsize : q.side≤(upperSide:ℝ))
    (hi : q.Inside x y) :
    |(w.c:ℝ)*(x-centerX q)+(w.s:ℝ)*(y-centerY q)|<(upperSide:ℝ)*w.outer/2 ∧
    |-(w.s:ℝ)*(x-centerX q)+(w.c:ℝ)*(y-centerY q)|<(upperSide:ℝ)*w.outer/2 := by
  have hpoint := (inside_centered_iff q x y).mp hi
  obtain ⟨hu0,hu1,hv0,hv1⟩ := hpoint
  have hb := w.support hw t ht0 ht1
  rw [←hc,←hs] at hb
  have he : -(w.c:ℝ)*q.s+(w.s:ℝ)*q.c= -(-(w.s:ℝ)*q.c+(w.c:ℝ)*q.s) := by ring
  have hbound : q.side*(|(w.c:ℝ)*q.c+(w.s:ℝ)*q.s|+|-(w.c:ℝ)*q.s+(w.s:ℝ)*q.c|)
      ≤(upperSide:ℝ)*w.outer := by
    rw [he,abs_neg]
    have h0 := mul_le_mul_of_nonneg_left hb q.side_pos.le
    have hout : 0≤(w.outer:ℝ) := by exact_mod_cast hw.2.2.2.1.le
    have h1 := mul_le_mul_of_nonneg_right hsize hout
    exact h0.trans h1
  apply normal_change_inner w.c w.s q.c q.s ((upperSide:ℝ)*w.outer) q.side
    (x-centerX q) (y-centerY q) (by
      have h := congrArg (fun r : ℚ => (r : ℝ)) hw.2.2.1
      simpa only [pow_two, Rat.cast_add, Rat.cast_mul, Rat.cast_one] using h)
    q.unit_normal q.side_pos hbound
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith

/-- All four wall constraints at the certified minimum width. -/
theorem AngleEnclosure.wall_sound (w : AngleEnclosure) (hw : w.Check)
    (lowerSide : ℚ) (ha : 0<lowerSide) (q : OpenSquare) (t : ℝ)
    (hc : q.c=normalC t) (hs : q.s=normalS t)
    (ht0 : (w.lower:ℝ)≤t) (ht1 : t≤(w.upper:ℝ))
    (hsize : (lowerSide:ℝ)≤q.side) (hbox : InsideContainer q) :
    (lowerSide:ℝ)*w.wall/2≤centerX q ∧ centerX q≤4-(lowerSide:ℝ)*w.wall/2 ∧
    (lowerSide:ℝ)*w.wall/2≤centerY q ∧ centerY q≤4-(lowerSide:ℝ)*w.wall/2 := by
  have ht0' : 0≤t := le_trans (by exact_mod_cast hw.1) ht0
  have ht1' : t≤1 := le_trans ht1 (by exact_mod_cast hw.2.1)
  have hn := normal_nonnegative t ht0' ht1'
  rw [←hc,←hs] at hn
  have hb := w.wall_bound hw t ht0 ht1
  rw [←hc,←hs] at hb
  have h0 := mul_le_mul_of_nonneg_left hb (by exact_mod_cast ha.le : (0:ℝ)≤lowerSide)
  have h1 := mul_le_mul_of_nonneg_right hsize (add_nonneg hn.1 hn.2)
  obtain ⟨hx0,hx1,hy0,hy1⟩ := positive_frame_all_walls q hn.1 hn.2 hbox
  exact ⟨by nlinarith only [h0,h1,hx0],by nlinarith only [h0,h1,hx1],
    by nlinarith only [h0,h1,hy0],by nlinarith only [h0,h1,hy1]⟩

#print axioms AngleEnclosure.outer_sound
#print axioms AngleEnclosure.wall_sound
end S12
