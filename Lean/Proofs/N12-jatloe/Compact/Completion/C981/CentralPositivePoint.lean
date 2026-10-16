import Compact.Completion.C981.HalfAngle
import S12.Convex
import S12.WallGeometry
import S12.ShortCluster.Projections

/-! Theorem 5 of C981-COMMON-CYCLE. The actual whole left-wall
segment forces a positive central square to own (2,2.62). -/
namespace N12Compact.C981CompletionCentralPositivePoint

open S12 S12Pilot
set_option Elab.async false

private theorem scalar (c s : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (order : s ≤ c)
    (unit : c^2+s^2=1) : (97/100)*c*s < c+s-1+(7/20)*s^2 := by
  have d := C981CompletionHalfAngle.data c s hc hs.le order unit
  let t := C981CompletionHalfAngle.half c s
  have tp : 0 < t := div_pos hs (by linarith only [hc])
  have remainder := mul_nonneg (show 0 ≤ 1/2-t by linarith only [d.2.1])
    (sq_nonneg t)
  have square := sq_nonneg (t-5/49)
  have bracket : 0 < 3/100-(3/10)*t+(197/100)*t^2-t^3 := by
    nlinarith only [remainder,square]
  have identity :
      (1+t^2)^2*(c+s-1+(7/20)*s^2-(97/100)*c*s) =
        2*t*(3/100-(3/10)*t+(197/100)*t^2-t^3) := by
    calc
      _ = (1+t^2)*((1+t^2)*c+(1+t^2)*s-(1+t^2)) +
          (7/20)*((1+t^2)*s)^2-(97/100)*((1+t^2)*c)*((1+t^2)*s) := by ring
      _ = _ := by rw [d.2.2.2.1,d.2.2.2.2]; ring
  have positive : 0 < 2*t*(3/100-(3/10)*t+(197/100)*t^2-t^3) :=
    mul_pos (by linarith only [tp]) bracket
  have scale : 0 ≤ (1+t^2)^2 := sq_nonneg _
  have gap : 0 < c+s-1+(7/20)*s^2-(97/100)*c*s :=
    pos_of_mul_pos_right (by rwa [identity]) scale
  linarith only [gap]

private theorem left_support (q : OpenSquare) (center : q.Inside 2 2)
    (avoid : ∀ y : ℝ, ¬ q.Inside 1 y) :
    1 ≤ q.c*q.loU-q.s*(q.loV+q.side) := by
  have inside_right (x y : ℝ) (point : q.Inside x y) : 1 ≤ x := by
    apply le_of_not_gt
    intro lower
    let t := (1-x)/(2-x)
    have denominator : 0 < 2-x := by linarith only [lower]
    have positive : 0 < t := div_pos (by linarith only [lower]) denominator
    have small : t < 1 := (div_lt_one denominator).mpr (by linarith)
    have intersection := inside_segment q x y 2 2 t point center positive.le small.le
    have relation : t*(2-x)=1-x := div_mul_cancel₀ _ denominator.ne'
    have identity : (1-t)*x+t*2=1 := by nlinarith only [relation]
    rw [identity] at intersection
    exact avoid _ intersection
  have support : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side)-1 := by
    apply affine_endpoint_nonnegative q.side (q.c+q.s) _ q.side_pos
    intro t positive small
    let u := q.loU+t
    let v := q.loV+q.side-t
    have point : q.Inside (q.c*u-q.s*v) (q.s*u+q.c*v) := by
      apply (inside_iff_rotated_box q _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have bound := inside_right _ _ point
    dsimp [u,v] at bound
    nlinarith only [bound]
  linarith only [support]

/-- Positive canonical frame, including the diagonal tie. Whole segment
absence is needed; its two endpoint absences alone do not suffice. -/
theorem point (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (center : q.Inside 2 2) (west : q.Inside (3/2) 2)
    (north : q.Inside 2 (5/2)) (marker : q.Inside (33/20) (47/20))
    (missingSW : ¬ q.Inside (33/20) (33/20))
    (missingNE : ¬ q.Inside (47/20) (47/20))
    (wallSegment : ∀ y : ℝ, 113/50 ≤ y → y ≤ 14/5 → ¬ q.Inside 1 y) :
    q.Inside 2 (131/50) := by
  have cone : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have rUlo : q.loU < (47/20)*(q.c+q.s) := by linarith only [center.1,hc,hs]
  have rVlo : q.loV < -(47/20)*q.s+(47/20)*q.c := by
    linarith only [center.2.2.1,order]
  have rVhi : -(47/20)*q.s+(47/20)*q.c < q.loV+q.side := by
    linarith only [marker.2.2.2,hs]
  have rFace : q.loU+q.side ≤ (47/20)*(q.c+q.s) :=
    le_of_not_gt (fun u => missingNE
      ⟨by linarith only [rUlo],by linarith only [u],by linarith only [rVlo],by linarith only [rVhi]⟩)
  have lUhi : (33/20)*(q.c+q.s) < q.loU+q.side := by
    linarith only [center.2.1,hc,hs]
  have lVhi : -(33/20)*q.s+(33/20)*q.c < q.loV+q.side := by
    linarith only [center.2.2.2,order]
  have lUlo : q.loU < (33/20)*(q.c+q.s) := by
    have short := (short_projections q (7/10) (7/10) (by norm_num)).2.1
    linarith only [rFace,short,side]
  have lFace : -(33/20)*q.s+(33/20)*q.c ≤ q.loV :=
    le_of_not_gt (fun v => missingSW
      ⟨by linarith only [lUlo],by linarith only [lUhi],by linarith only [v],by linarith only [lVhi]⟩)
  have xUlo : q.loU < 2*q.c+(131/50)*q.s := by linarith only [north.1,hs]
  have xVlo : q.loV < -2*q.s+(131/50)*q.c := by linarith only [north.2.2.1,hc]
  have xVhi : -2*q.s+(131/50)*q.c < q.loV+q.side := by
    linarith only [lFace,cone,hs,side]
  have xUhi : 2*q.c+(131/50)*q.s < q.loU+q.side := by
    apply lt_of_not_ge
    intro cap
    have sine : 0 < q.s := by linarith only [cap,center.2.1]
    have jVlo : q.loV < -q.s+(113/50)*q.c := by
      linarith only [west.2.2.1,hc,hs]
    have jUhi : q.c+(113/50)*q.s < q.loU+q.side := by
      linarith only [north.2.1,hc,hs]
    have jVhi : -q.s+(113/50)*q.c < q.loV+q.side := by
      have short := (short_projections q (-(13/20)) (61/100) (by norm_num)).2.2.2
      linarith only [lFace,short,side]
    have jFace : q.c+(113/50)*q.s ≤ q.loU :=
      le_of_not_gt (fun u => wallSegment (113/50) le_rfl (by norm_num)
        ⟨by linarith only [u],
          by linarith only [jUhi],
          by linarith only [jVlo],
          by linarith only [jVhi]⟩)
    have kVlo : q.loV < -q.s+(14/5)*q.c := by
      linarith only [west.2.2.1,hc,hs]
    have kUhi : q.c+(14/5)*q.s < q.loU+q.side := by
      linarith only [north.2.1,hc,order]
    have kUlo : q.loU < q.c+(14/5)*q.s := by
      linarith only [cap,side,cone,hs]
    have kFace : q.loV+q.side ≤ -q.s+(14/5)*q.c :=
      le_of_not_gt (fun v => wallSegment (14/5) (by norm_num) le_rfl
        ⟨by linarith only [kUlo],
          by linarith only [kUhi],
          by linarith only [kVlo],
          by linarith only [v]⟩)
    have noVertical : ∀ y : ℝ, ¬ q.Inside 1 y := by
      intro y point
      have yLow : 113/50 < y := by
        have projection : 0 < q.s*(y-113/50) := by
          linarith only [point.1,jFace]
        exact (sub_pos.mp (pos_of_mul_pos_right projection hs))
      have yHigh : y < 14/5 := by
        have projection : 0 < q.c*(14/5-y) := by
          linarith only [point.2.2.2,kFace]
        exact (sub_pos.mp (pos_of_mul_pos_right projection hc.le))
      exact wallSegment y yLow.le yHigh.le point
    have support := left_support q center noVertical
    have capProduct := mul_nonneg hc.le (sub_nonneg.mpr cap)
    have faceProduct := mul_nonneg hs (sub_nonneg.mpr lFace)
    have bound : q.side*(q.c+q.s) ≤ 1+(97/100)*q.c*q.s-(7/20)*q.s^2 := by
      nlinarith only [support,capProduct,faceProduct,q.unit_normal]
    have arc := scalar q.c q.s hc.le sine order q.unit_normal
    have strict := mul_pos (sub_pos.mpr side) (show 0 < q.c+q.s by linarith only [hc,hs])
    nlinarith only [bound,arc,strict]
  exact ⟨by linarith only [xUlo],by linarith only [xUhi],by linarith only [xVlo],by linarith only [xVhi]⟩

#print axioms point
end N12Compact.C981CompletionCentralPositivePoint
