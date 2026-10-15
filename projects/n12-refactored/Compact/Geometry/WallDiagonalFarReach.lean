import Compact.Geometry.WallStrongerLowerReach
import Compact.Geometry.C977CornerCubic

/-! A diagonal foreign corner seed pushes a positive canonical left
wall to height 2.86. After coordinate interchange this is the genuine
nonpositive bottom-wall sector, not an all-angle reach assertion. -/
namespace N12Compact.WallDiagonalFarReach

open S12 S12Pilot FourSquareAnchors C977CornerCubic
set_option Elab.async false

private theorem margin {c s : ℝ} (normal : Normal c s) :
    0≤c+s-1-(9/10)*c*s+(6/25)*s^2 := by
  have bounds := normal_bounds normal
  have defect : 0≤1-c := by linarith only [bounds.2.1]
  have lower : (1/2)*s^2≤1-c := by
    nlinarith only [normal.2.2,sq_nonneg (1-c)]
  have upper : 1-c≤(3/5)*s^2 := by
    have product := mul_nonneg defect
      (show 0≤(3/5)*c-2/5 by linarith only [bounds.1])
    nlinarith only [normal.2.2,product]
  have lowerScaled := mul_nonneg normal.1 (sub_nonneg.mpr lower)
  have square := mul_nonneg normal.1 (sq_nonneg (s-2/5))
  nlinarith only [upper,lowerScaled,square,normal.1]

/-- Full containment and the two actual foreign points close every face
escape of the farther target for this canonical sign. -/
theorem point (q : OpenSquare) (normal : Normal q.c q.s)
    (side : 1<q.side) (box : InsideContainer q)
    (marker : q.Inside (457/500) 2) (high : q.Inside 1 (12/5))
    (missingFar : ¬q.Inside (19/25) (49/25))
    (missingInward : ¬q.Inside (3/2) 2) : q.Inside 1 (143/50) := by
  have bounds := normal_bounds normal
  have hc : 0≤q.c := by linarith only [bounds.1]
  have wall : 0≤q.c*q.loU-q.s*(q.loV+q.side) := by
    have lower : ∀ x y, q.Inside x y→0≤x ∧ 0≤y := by
      intro x y h
      have contained := box x y h
      exact ⟨contained.1,contained.2.2.1⟩
    have boundary := (positive_frame_wall_bounds q hc normal.1 lower).1
    dsimp [centerX] at boundary
    nlinarith only [boundary]
  have targetUlo : q.loU<q.c+(143/50)*q.s := by
    nlinarith only [marker.1,hc,normal.1]
  have targetVlo : q.loV< -q.s+(143/50)*q.c := by
    nlinarith only [high.2.2.1,hc]
  have farUhi : (19/25)*q.c+(49/25)*q.s<q.loU+q.side := by
    nlinarith only [marker.2.1,hc,normal.1]
  have farVhi : -(19/25)*q.s+(49/25)*q.c<q.loV+q.side := by
    nlinarith only [high.2.2.2,hc,normal.1,normal.2.1]
  have farFaces : (19/25)*q.c+(49/25)*q.s≤q.loU ∨
      -(19/25)*q.s+(49/25)*q.c≤q.loV := by
    by_cases lowerU : (19/25)*q.c+(49/25)*q.s≤q.loU
    · exact Or.inl lowerU
    · right
      apply le_of_not_gt
      intro lowerV
      apply missingFar
      refine ⟨?_,farUhi,lowerV,farVhi⟩
      linarith only [lowerU]
  have shortFar := short_projections q (6/25) (9/10) (by norm_num)
  rcases farFaces with lowerU | lowerV
  · have shortInward := (short_projections q (37/50) (1/25) (by norm_num)).2.1
    have inwardVlo : -(3/2)*q.s+2*q.c≤q.loV := by
      apply le_of_not_gt
      intro insideLow
      apply missingInward
      refine ⟨?_,?_,insideLow,?_⟩
      · nlinarith only [marker.1,hc]
      · linarith only [lowerU,shortInward,side]
      · nlinarith only [high.2.2.2,hc,normal.1]
    have shortDiagonal :=
      (short_projections q (-(1/2)) (43/50) (by norm_num)).2.2.2
    refine ⟨targetUlo,?_,targetVlo,?_⟩
    · linarith only [lowerU,shortFar.2.1,side]
    · linarith only [inwardVlo,shortDiagonal,side]
  · have lowerProduct := mul_nonneg normal.1 (sub_nonneg.mpr lowerV)
    have strict := mul_pos (sub_pos.mpr side)
      (show 0<q.c+q.s by linarith only [bounds.2.2.2.2.1])
    have targetUhi : q.c+(143/50)*q.s<q.loU+q.side := by
      apply lt_of_not_ge
      intro cap
      have upperProduct := mul_nonneg hc (sub_nonneg.mpr cap)
      have residual := margin normal
      nlinarith only [wall,lowerProduct,strict,upperProduct,residual,q.unit_normal]
    refine ⟨targetUlo,targetUhi,targetVlo,?_⟩
    linarith only [lowerV,shortFar.2.2.2,side]

#print axioms point
end N12Compact.WallDiagonalFarReach
