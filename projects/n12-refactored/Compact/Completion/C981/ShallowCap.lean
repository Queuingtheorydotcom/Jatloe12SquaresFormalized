import Compact.Completion.C981.TopReach
import Compact.Completion.C981.HalfAngle
import S12.Convex

/-! The actual shallow circular cap in C981 row 71. In a positive
canonical frame the central owner has the nearby tip. In a negative
frame it strictly owns every point of Cap, including the circular edge. -/
namespace N12Compact.C981CompletionShallowCap

open S12 S12Pilot C977CornerCubic
set_option Elab.async false

def Cap (x y : ℝ) : Prop :=
  -(13/50) ≤ x ∧ x ≤ 0 ∧ -(69/2000) ≤ y ∧ y ≤ 0 ∧
    (x+13/50)^2+(y+1)^2 ≤ 1

theorem arc828 {c s : ℝ} (normal : Normal c s) :
    1+(207/250)*c*s ≤ c+s := by
  have bounds := normal_bounds normal
  have high : c+s ≤ 283/200 := by
    nlinarith only [normal.2.2,sq_nonneg (c-s),sq_nonneg (c+s-283/200)]
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1)
    (sub_nonneg.mpr high)
  have cross := mul_nonneg (show 0 ≤ c by linarith only [bounds.1]) normal.1
  nlinarith only [product,normal.2.2,cross]

private theorem left_support (q : OpenSquare) (anchor : q.Inside 0 (-(37/50)))
    (avoid : ∀ y : ℝ, ¬ q.Inside (-1) y) :
    -1 ≤ q.c*q.loU-q.s*(q.loV+q.side) := by
  have inside_right (x y : ℝ) (point : q.Inside x y) : -1 ≤ x := by
    apply le_of_not_gt
    intro lower
    let t := (-1-x)/(-x)
    have denominator : 0 < -x := by linarith only [lower]
    have positive : 0 < t := div_pos (by linarith only [lower]) denominator
    have small : t < 1 := (div_lt_one denominator).mpr (by linarith)
    have intersection := inside_segment q x y 0 (-(37/50)) t point anchor positive.le small.le
    have relation : t*(-x)=-1-x := div_mul_cancel₀ _ denominator.ne'
    have identity : (1-t)*x+t*0=-1 := by nlinarith only [relation]
    rw [identity] at intersection
    exact avoid _ intersection
  have support : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side)+1 := by
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

theorem positive_tip (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (f : q.Inside (-(13/50)) 0) (a : q.Inside 0 (-(37/50)))
    (missingO : ¬ q.Inside 0 0) (missingB : ¬ q.Inside (-(13/50)) (-1))
    (segment : ∀ y : ℝ, -(37/50) ≤ y → y ≤ -(1/5) → ¬ q.Inside (-1) y) :
    q.Inside (-(3/100)) 0 := by
  have normal : Normal q.c q.s := ⟨hs,order,q.unit_normal⟩
  have oLowU : q.loU < 0 := by linarith only [f.1,hc]
  have oLowV : q.loV < 0 := by linarith only [a.2.2.1,hc]
  have oHighV : 0 < q.loV+q.side := by linarith only [f.2.2.2,hs]
  have oFace : q.loU+q.side ≤ 0 := by
    apply le_of_not_gt
    intro high
    apply missingO
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [oLowU,high,oLowV,oHighV]
  have projection := C981CompletionWallScalars.canonical_projection q.c q.s hc.le hs order q.unit_normal
  have bLowU : q.loU < -(13/50)*q.c-q.s := by linarith only [oFace,side,projection,hc]
  have bHighU : -(13/50)*q.c-q.s < q.loU+q.side := by linarith only [f.2.1,hs]
  have bHighV : (13/50)*q.s-q.c < q.loV+q.side := by linarith only [f.2.2.2,hc]
  have bFace : (13/50)*q.s-q.c ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply missingB
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bLowU,bHighU,low,bHighV]
  have xLowU : q.loU < -(3/100)*q.c := by linarith only [f.1,hc]
  have xLowV : q.loV < (3/100)*q.s := by linarith only [a.2.2.1,hc,hs]
  have xHighV : (3/100)*q.s < q.loV+q.side := by linarith only [f.2.2.2,hs]
  have xHighU : -(3/100)*q.c < q.loU+q.side := by
    apply lt_of_not_ge
    intro cap
    have sp : 0 < q.s := by linarith only [cap,a.2.1,hc]
    have lHighU : -q.c-(1/5)*q.s < q.loU+q.side := by linarith only [f.2.1,hc,hs]
    have lLowV : q.loV < q.s-(1/5)*q.c := by linarith only [a.2.2.1,hc,hs]
    have short := (short_projections q (97/100) (1/5) (by norm_num)).2.1
    have lLowU : q.loU < -q.c-(1/5)*q.s := by linarith only [cap,short,side]
    have lFace : q.loV+q.side ≤ q.s-(1/5)*q.c := by
      apply le_of_not_gt
      intro high
      apply segment (-(1/5)) (by norm_num) le_rfl
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lLowU,lHighU,lLowV,high]
    have jHighU : -q.c-(37/50)*q.s < q.loU+q.side := by linarith only [a.2.1,hc]
    have jLowV : q.loV < q.s-(37/50)*q.c := by linarith only [a.2.2.1,hs]
    have jHighV : q.s-(37/50)*q.c < q.loV+q.side := by
      have small := (short_projections q (-(37/50)) (13/50) (by norm_num)).2.2.2
      linarith only [bFace,small,side]
    have jFace : -q.c-(37/50)*q.s ≤ q.loU := by
      apply le_of_not_gt
      intro low
      apply segment (-(37/50)) le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,jHighU,jLowV,jHighV]
    have noVertical : ∀ y : ℝ, ¬ q.Inside (-1) y := by
      intro y point
      have low : -(37/50) < y := by
        have product : 0 < q.s*(y+37/50) := by linarith only [point.1,jFace]
        exact (sub_pos.mp (pos_of_mul_pos_right (by convert product using 1 <;> ring) hs))
      have high : y < -(1/5) := by
        have product : 0 < q.c*(-(1/5)-y) := by linarith only [point.2.2.2,lFace]
        exact (sub_pos.mp (pos_of_mul_pos_right product hc.le))
      exact segment y low.le high.le point
    have support := left_support q a noVertical
    have one := mul_nonneg hc.le (sub_nonneg.mpr cap)
    have two := mul_nonneg hs (sub_nonneg.mpr bFace)
    have upper : q.side*(q.c+q.s) ≤
        1-(3/100)*q.c^2-(13/50)*q.s^2+q.c*q.s := by
      nlinarith only [support,one,two,q.unit_normal]
    have curved := arc828 normal
    have square := sq_nonneg (q.c-(43/15)*q.s)
    have gap : 0 < (3/100)*q.c^2+(13/50)*q.s^2-(43/250)*q.c*q.s := by
      nlinarith only [square,mul_pos sp sp]
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [hc,hs])
    nlinarith only [upper,curved,gap,strict]
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [xLowU,xHighU,xLowV,xHighV]

theorem negative_cap (q : OpenSquare) (side : 1 < q.side)
    (hc : 0 < q.c) (hs : q.s ≤ 0) (order : -q.s ≤ q.c)
    (f : q.Inside (-(13/50)) 0) (a : q.Inside 0 (-(37/50)))
    (missingB : ¬ q.Inside (-(13/50)) (-1)) :
    ∀ x y, Cap x y → q.Inside x y := by
  have bLowU : q.loU < -(13/50)*q.c-q.s := by linarith only [f.1,hs]
  have bHighU : -(13/50)*q.c-q.s < q.loU+q.side := by linarith only [a.2.1,order]
  have bHighV : (13/50)*q.s-q.c < q.loV+q.side := by linarith only [f.2.2.2,hc]
  have bFace : (13/50)*q.s-q.c ≤ q.loV := by
    apply le_of_not_gt
    intro low
    apply missingB
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bLowU,bHighU,low,bHighV]
  intro x y cap
  have dx := mul_nonneg hc.le (show 0 ≤ x+13/50 by linarith only [cap.1])
  have ys := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
    (show 0 ≤ -y by linarith only [cap.2.2.2.1])
  have xLowU : q.loU < q.c*x+q.s*y := by nlinarith only [f.1,dx,ys]
  have xx := mul_nonneg hc.le (show 0 ≤ -x by linarith only [cap.2.1])
  have ya := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
    (show 0 ≤ y+37/50 by linarith only [cap.2.2.1])
  have xHighU : q.c*x+q.s*y < q.loU+q.side := by nlinarith only [a.2.1,xx,ya]
  have xs := mul_nonneg (show 0 ≤ -q.s by linarith only [hs])
    (show 0 ≤ x+13/50 by linarith only [cap.1])
  have yy := mul_nonneg hc.le (show 0 ≤ y+69/2000 by linarith only [cap.2.2.1])
  have xLowV : q.loV < -q.s*x+q.c*y := by
    nlinarith only [a.2.2.1,xs,yy,order,hc]
  let d := x+13/50
  let e := y+1
  have disk : d^2+e^2 ≤ 1 := cap.2.2.2.2
  have identity : (-q.s*d+q.c*e)^2+(q.c*d+q.s*e)^2=d^2+e^2 := by
    calc
      _ = (q.c^2+q.s^2)*(d^2+e^2) := by ring
      _ = _ := by rw [q.unit_normal]; ring
  have projection : -q.s*d+q.c*e ≤ 1 := by
    nlinarith only [disk,identity,sq_nonneg (q.c*d+q.s*e),sq_nonneg (-q.s*d+q.c*e-1)]
  have xHighV : -q.s*x+q.c*y < q.loV+q.side := by
    dsimp [d,e] at projection
    linarith only [projection,bFace,side]
  exact ⟨xLowU,xHighU,xLowV,xHighV⟩

#print axioms positive_tip
#print axioms negative_cap
end N12Compact.C981CompletionShallowCap
