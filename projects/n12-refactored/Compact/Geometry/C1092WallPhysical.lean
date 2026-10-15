import Compact.Geometry.C1092WallCenterCover
import S12.WallNormalBounds
import S12.WallGeometry

/-! Source-only physical adapter for the C1092 wall polygon. The proof uses
actual open squares and original markers, with arbitrary orientations and
closed center-sign boundaries. No Lean replay has been run for this file. -/

namespace N12Compact.C1092WallPhysical

open S12 S12Pilot C1092WallPolynomial

/-- The normalized form of the uniform quartic support calculation. -/
theorem target_quadratic_support (i : Fin 12) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hn : c^2+s^2=1) :
    targetX i*c^2+(457/500)*s^2+(targetY i-1)*c*s ≤ c+s := by
  obtain ⟨t,ht0,ht1,hst,hct⟩ := first_quadrant_rational s c hs hc (by nlinarith only [hn])
  have hden : 0 < 1+t^2 := by nlinarith [sq_nonneg t]
  have hm := region_margin _ _ _ (target_region i) ht0 ht1
  have hid : (c+s-(targetX i*c^2+(457/500)*s^2+(targetY i-1)*c*s))*(1+t^2)^2 =
      margin (targetX i) (2-targetY i) t := by
    rw [hct,hst]
    dsimp [margin]
    field_simp [ne_of_gt hden]
    ring
  have hp : 0 ≤ (c+s-(targetX i*c^2+(457/500)*s^2+(targetY i-1)*c*s))*(1+t^2)^2 := by
    rw [hid]; exact hm
  have h := nonneg_of_mul_nonneg_left hp (sq_pos_of_pos hden)
  linarith only [h]

/-- The normalized rectangle bound for the negative-V face. -/
theorem rectangle_support (x h c s : ℝ) (hx : x ≤ 1) (hh : h ≤ 197/500)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hn : c^2+s^2=1) :
    2*(x*s+h*c) ≤ 1+s*(c+s) := by
  obtain ⟨t,ht0,ht1,hst,hct⟩ := first_quadrant_rational s c hs hc (by nlinarith only [hn])
  have hden : 0 < 1+t^2 := by nlinarith [sq_nonneg t]
  have hp := mul_nonneg (show 0 ≤ 2*(1-t) by linarith only [ht1])
    (pface2_cubic_nonneg t ht1)
  have hid : (1+s*(c+s)-2*(s+(197/500)*c))*(1+t^2)^2 =
      2*(1-t)*((53/500:ℝ)-(447/500)*t+(1053/500)*t^2-(447/500)*t^3) := by
    rw [hct,hst]
    field_simp [ne_of_gt hden]
    ring
  have hbase : 0 ≤ 1+s*(c+s)-2*(s+(197/500)*c) := by
    apply nonneg_of_mul_nonneg_left (b := (1+t^2)^2) _ (sq_pos_of_pos hden)
    rw [hid]; exact hp
  have hxs := mul_nonneg (sub_nonneg.mpr hx) hs
  have hhc := mul_nonneg (sub_nonneg.mpr hh) hc
  nlinarith only [hbase,hxs,hhc]

/-- The X≤1 physical branch. The marker A chooses the two boundary exit
faces and the three target exit faces; the uniform inequalities exclude
each resulting possibility, retaining equality at every boundary. -/
theorem positive_frame_left_point (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (wall : q.side*(q.c+q.s)/2 ≤ centerX q)
    (hx : centerX q ≤ 1) (hy : centerY q ≤ 2)
    (owned : q.Inside (457/500) 2) (outsideB : ¬ q.Inside (457/500) 1)
    (i : Fin 12) : q.Inside (targetX i) (targetY i) := by
  have hA := (inside_centered_iff q (457/500) 2).mp owned
  have hB : ¬ InBands (-q.side/2) (-q.side/2) q.side
      (q.c*(457/500-centerX q)+q.s*(1-centerY q))
      (-q.s*(457/500-centerX q)+q.c*(1-centerY q)) := by
    simpa only [← inside_centered_iff] using outsideB
  have hBfaces :
      q.c*(457/500-centerX q)+q.s*(1-centerY q) ≤ -q.side/2 ∨
      -q.s*(457/500-centerX q)+q.c*(1-centerY q) ≤ -q.side/2 := by
    simp only [InBands,not_and_or,not_lt] at hB
    dsimp [InBands] at hA
    rcases hB with h | h | h | h
    · exact Or.inl h
    · nlinarith only [h,hA.2.1,hs]
    · exact Or.inr h
    · nlinarith only [h,hA.2.2.2,hc]
  obtain ⟨hxb,hx1,hy2,harea,hBP,hDP,hFP,hdisk⟩ :=
    C1092WallCenterCover.target_cover_arithmetic i
  have hhalf := target_half_distance i
  have hhalfScaled : (2*(1-targetX i))^2+(2*(2-targetY i))^2 ≤ 1 := by
    nlinarith only [hhalf]
  have hprojectionHalf := (short_projections q _ _ hhalfScaled).2.1
  have hprojectionOne := (short_projections q _ _ hBP).2.1
  have hquad := target_quadratic_support i q.c q.s hc hs q.unit_normal
  have hrect := rectangle_support (targetX i) (2-targetY i) q.c q.s
    (target_rectangle i).1 (target_rectangle i).2 hc hs q.unit_normal
  have hcx := mul_nonneg hc (sub_nonneg.mpr hx)
  have hsy := mul_nonneg hs (sub_nonneg.mpr hy)
  have hcy := mul_nonneg hc (sub_nonneg.mpr hy)
  have hxs := mul_nonneg hs (sub_nonneg.mpr hxb)
  have hhc := mul_nonneg hc (sub_nonneg.mpr hy2)
  have hcs : 0 < q.c+q.s := by
    by_contra h
    have hz : q.c=0 ∧ q.s=0 := by constructor <;> linarith
    nlinarith only [q.unit_normal,hz.1,hz.2]
  have hstrict := mul_pos (sub_pos.mpr ha) hcs
  have hsfactor : 0 < 1+q.s*(q.c+q.s) := by
    have hp := mul_nonneg hs (add_nonneg hc hs)
    linarith
  have hstrictS := mul_pos (sub_pos.mpr ha) hsfactor
  by_contra outsideP
  have hP : ¬ InBands (-q.side/2) (-q.side/2) q.side
      (q.c*(targetX i-centerX q)+q.s*(targetY i-centerY q))
      (-q.s*(targetX i-centerX q)+q.c*(targetY i-centerY q)) := by
    simpa only [← inside_centered_iff] using outsideP
  simp only [InBands,not_and_or,not_lt] at hP
  dsimp [InBands] at hA
  rcases hP with hP | hP | hP | hP
  · nlinarith only [hP,hprojectionHalf,hcx,hsy,ha]
  · rcases hBfaces with hB | hB
    · nlinarith only [hP,hB,hprojectionOne,ha]
    · have hPc := mul_nonneg hc (show 0 ≤
          q.c*(targetX i-centerX q)+q.s*(targetY i-centerY q)-q.side/2 by linarith only [hP])
      have hBs := mul_nonneg hs (show 0 ≤
          q.s*(457/500-centerX q)-q.c*(1-centerY q)-q.side/2 by linarith only [hB])
      have hunitX : q.c^2*centerX q+q.s^2*centerX q=centerX q := by
        calc
          _ = (q.c^2+q.s^2)*centerX q := by ring
          _ = _ := by rw [q.unit_normal,one_mul]
      nlinarith only [hPc,hBs,hunitX,wall,hquad,hstrict]
  · have hswall := mul_le_mul_of_nonneg_left wall hs
    nlinarith only [hP,hswall,hcy,hrect,hstrictS]
  · nlinarith only [hP,hA.2.2.2,hxs,hhc]

/-- Complete physical wall-point entrance for the original C1092 marker12
owner in the selected closed sign branch. All orientations are covered by
face reindexing, and both sides of X=1 are proved from their actual geometry.
This is a compulsory-point theorem, not a whole-case exclusion. -/
theorem original_wall_point (q : OpenSquare) (ha : 1 < q.side)
    (cap : q.side ≤ 1001/1000) (hbox : InsideContainer q)
    (owned : q.Inside (457/500) 2)
    (outside0 : ¬ q.Inside 1 (457/500))
    (outside1 : ¬ q.Inside (457/500) 1)
    (outside8 : ¬ q.Inside (33/20) (33/20))
    (outside11 : ¬ q.Inside (33/20) (47/20))
    (hy : centerY q ≤ 2) (i : Fin 12) :
    q.Inside (targetX i) (targetY i) := by
  by_cases hx : centerX q ≤ 1
  · obtain ⟨r,hc,hs,hside,hX,hY,hinside⟩ := exists_positive_frame q
    have hrbox : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y := by
      intro x y h
      have hp := hbox x y ((hinside x y).mp h)
      exact ⟨hp.1,hp.2.2.1⟩
    have hrwall := (positive_frame_wall_bounds r hc hs hrbox).1
    apply (hinside _ _).mp
    apply positive_frame_left_point r (by simpa only [hside] using ha) hc hs hrwall
      (by simpa only [hX] using hx) (by simpa only [hY] using hy)
      ((hinside _ _).mpr owned) _ i
    exact fun h => outside1 ((hinside _ _).mp h)
  · exact C1092WallCenterCover.original_right_branch_point q ha cap owned
      outside0 outside1 outside8 outside11 (lt_of_not_ge hx).le hy i

/-- A singleton marker12 owner has one of the two actual compulsory point
families, according to its center sign. Reflection transports the physical
square and the original foreign markers; equality at Y=2 is retained. -/
theorem singleton_wall_point_cover (q : OpenSquare) (ha : 1 < q.side)
    (cap : q.side ≤ 1001/1000) (hbox : InsideContainer q)
    (owned : Owns q 12) (missing : ∀ j : Marker, j ≠ 12 → ¬ Owns q j) :
    (centerY q ≤ 2 ∧ ∀ i : Fin 12, q.Inside (targetX i) (targetY i)) ∨
    (2 ≤ centerY q ∧ ∀ i : Fin 12, q.Inside (targetX i) (4-targetY i)) := by
  have hA : q.Inside (457/500) 2 := by simpa [Owns,marker] using owned
  have h0 : ¬ q.Inside 1 (457/500) := by
    simpa [Owns,marker] using missing 0 (by decide)
  have h1 : ¬ q.Inside (457/500) 1 := by
    simpa [Owns,marker] using missing 1 (by decide)
  have h6 : ¬ q.Inside 1 (1543/500) := by
    simpa [Owns,marker] using missing 6 (by decide)
  have h7 : ¬ q.Inside (457/500) 3 := by
    simpa [Owns,marker] using missing 7 (by decide)
  have h8 : ¬ q.Inside (33/20) (33/20) := by
    simpa [Owns,marker] using missing 8 (by decide)
  have h11 : ¬ q.Inside (33/20) (47/20) := by
    simpa [Owns,marker] using missing 11 (by decide)
  by_cases hy : centerY q ≤ 2
  · exact Or.inl ⟨hy,fun i => original_wall_point q ha cap hbox hA h0 h1 h8 h11 hy i⟩
  · refine Or.inr ⟨(lt_of_not_ge hy).le,?_⟩
    intro i
    apply (inside_pullY q _ _).mp
    apply original_wall_point (pullY q) ha cap (container_pullY q hbox)
    · simpa only [inside_pullY,show (4:ℝ)-2=2 by norm_num] using hA
    · convert h6 using 1 <;> norm_num [inside_pullY]
    · simpa only [inside_pullY,show (4:ℝ)-1=3 by norm_num] using h7
    · convert h11 using 1 <;> norm_num [inside_pullY]
    · convert h8 using 1 <;> norm_num [inside_pullY]
    · simp only [center_pullY_y]
      linarith only [lt_of_not_ge hy]

#print axioms original_wall_point
#print axioms singleton_wall_point_cover

end N12Compact.C1092WallPhysical
