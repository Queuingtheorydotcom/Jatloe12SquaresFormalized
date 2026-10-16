import Compact.Geometry.PositiveCentralNegativeBottom

/-! The surviving negative-bottom separator gives a genuine horizontal
support bound for the positive central square. This does not assert the
false three-square left-point implication: the actual central square is
proved to lie above y=1, and its remaining wall interactions stay open. -/
namespace N12Compact.PositiveCentralNegativeFloor

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem boundary_margin {c t : ℝ} (normal : Normal c t) :
    c+(8/5)*t ≤ boundary c t := by
  have b := normal_bounds normal
  have hc : 0<c := by linarith only [b.1]
  have arc := mul_nonneg
    (show 0≤c+t-1 by linarith only [b.2.2.2.2.1])
    (show 0≤3/2-(c+t) by linarith only [b.2.2.2.2.2])
  have product := mul_nonneg hc.le normal.1
  have chord : (4/5)*c*t≤c+t-1 := by
    nlinarith only [arc,normal.2.2]
  have exactBoundary : c*boundary c t=c+c*t+t-t^2 := by
    unfold boundary
    field_simp [hc.ne']
    ring
  have scaled : 0≤c*(boundary c t-c-(8/5)*t) := by
    nlinarith only [exactBoundary,normal.2.2,chord,product]
  have gap := nonneg_of_mul_nonneg_right scaled hc
  linarith only [gap]

/-- A central square above the true negative-bottom face has all of its
horizontal lower support strictly above 1. Only the original center-face
cap is used; no left-point ownership is assumed or concluded. -/
theorem of_separation (O A : OpenSquare) (t : ℝ)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (side : 1≤A.side)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (face : boundary O.c t<O.loV+O.side)
    (sep : O.loV+O.side≤lower A t O.c) :
    1<lower A 0 1 := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have oc : 0<O.c := by linarith only [ob.1]
  have ac : 0<A.c := by linarith only [ab.1]
  let K := O.c*A.c-t*A.s
  let D := t*A.c+O.c*A.s
  have kp : 0≤K := by
    have first := mul_nonneg oc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]
    nlinarith only [first,second]
  have dp : 0≤D := add_nonneg (mul_nonneg on.1 ac.le)
    (mul_nonneg oc.le an.1)
  have floorForm : lower A 0 1=A.s*A.loU+A.c*A.loV := by
    rw [lower_in_bands]
    simp only [zero_mul,one_mul,neg_zero,zero_add,add_zero,
      abs_of_nonneg an.1,abs_of_nonneg ac.le]
    ring
  have directionForm : lower A t O.c=D*A.loU+K*A.loV := by
    rw [lower_in_bands]
    have coefficient : -t*A.s+O.c*A.c=K := by dsimp [K]; ring
    rw [coefficient]
    change D*(A.loU+A.side/2)+K*(A.loV+A.side/2)-
      A.side/2*(|D|+|K|)=D*A.loU+K*A.loV
    rw [abs_of_nonneg dp,abs_of_nonneg kp]
    ring
  by_contra failure
  have floorLow : A.s*A.loU+A.c*A.loV≤1 := by
    rw [floorForm] at failure
    exact le_of_not_gt failure
  have floorWeight := mul_nonneg kp (sub_nonneg.mpr floorLow)
  have upperWeight := mul_nonneg on.1
    (show 0≤2*(A.c+A.s)-1-A.loU by linarith only [cap,side])
  have identity :
      A.c*(D*A.loU+K*A.loV)=
        t*A.loU+K*(A.s*A.loU+A.c*A.loV) := by
    dsimp [D,K]
    linear_combination (t*A.loU)*an.2.2
  have upper : A.c*lower A t O.c≤
      O.c*A.c+t*(2*A.c+A.s-1) := by
    rw [directionForm]
    have kValue : K = O.c*A.c-t*A.s := rfl
    clear_value D K
    nlinarith only [identity,floorWeight,upperWeight,kValue]
  have centralArc : A.s+(2/5)*A.c≤1 := by
    linarith only [an.2.1,ab.2.2.2.2.2]
  have angleWeight := mul_nonneg on.1 (sub_nonneg.mpr centralArc)
  have boundaryWeight := mul_nonneg ac.le
    (sub_nonneg.mpr (boundary_margin on))
  have bound : O.c*A.c+t*(2*A.c+A.s-1)≤A.c*boundary O.c t := by
    nlinarith only [angleWeight,boundaryWeight]
  have strict := mul_lt_mul_of_pos_left (lt_of_lt_of_le face sep) ac
  linarith only [upper,bound,strict]

/-- Original bottom-singleton ownership and containment provide the face
premise of `of_separation`; no numerical pose ancestry is involved. -/
theorem actual (O A : OpenSquare) (t : ℝ) (os : O.s=-t)
    (on : Normal O.c t) (an : Normal A.c A.s)
    (oSide : 1<O.side) (aSide : 1≤A.side)
    (box : InsideContainer O)
    (marker : O.Inside 1 (457/500))
    (near : O.Inside (28/25) 1)
    (far : O.Inside (187/100) (19/25))
    (corner : ¬O.Inside 1 1)
    (cap : A.loU+A.side≤2*(A.c+A.s))
    (sep : O.loV+O.side≤lower A t O.c) :
    1<lower A 0 1 := by
  exact of_separation O A t on an aSide cap
    (corner_face O t os on oSide box marker near far corner).2.2 sep

/-- The real floor forces a useful strict point at x=6/5. Unlike x=1,
this point follows without any fourth-square assumption. -/
theorem inner_left_point (A : OpenSquare) (normal : Normal A.c A.s)
    (side : 1<A.side) (cap : A.loU+A.side≤2*(A.c+A.s))
    (floor : 1<A.s*A.loU+A.c*A.loV)
    (marker : A.Inside (33/20) (33/20))
    (west : A.Inside (3/2) 2) : A.Inside (6/5) 2 := by
  have b := normal_bounds normal
  have hc : 0<A.c := by linarith only [b.1]
  have arc := mul_nonneg
    (show 0≤A.c+A.s-1 by linarith only [b.2.2.2.2.1])
    (show 0≤3/2-(A.c+A.s) by linarith only [b.2.2.2.2.2])
  have chord : 0≤A.c+A.s-1-(4/5)*A.c*A.s := by
    nlinarith only [arc,normal.2.2]
  have upperWeight := mul_nonneg normal.1 (sub_nonneg.mpr cap)
  have width := mul_pos
    (show 0<A.c+A.s by linarith only [hc,normal.1]) (sub_pos.mpr side)
  have identity :
      A.c*(A.loV+A.side-(2*A.c-(6/5)*A.s)) =
      (A.s*A.loU+A.c*A.loV-1)+
      A.s*(2*(A.c+A.s)-A.side-A.loU)+
      (A.c+A.s)*(A.side-1)+(A.c+A.s-1-(4/5)*A.c*A.s) := by
    linear_combination (-2)*normal.2.2
  have scaled : 0<A.c*(A.loV+A.side-(2*A.c-(6/5)*A.s)) := by
    nlinarith only [identity,floor,upperWeight,width,chord]
  have high := pos_of_mul_pos_right scaled hc.le
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [cap,side,b.2.1]
  · linarith only [west.2.1,hc]
  · linarith only [marker.2.2.1,hc,normal.1]
  · linarith only [high]

/-- The same actual floor and center escape force the complete square to
reach strictly to the left of x=1. This alone is not a foreign-square
intersection: the height of that section must still be controlled. -/
theorem left_support (A : OpenSquare) (normal : Normal A.c A.s)
    (side : 1<A.side) (cap : A.loU+A.side≤2*(A.c+A.s))
    (floor : 1≤A.s*A.loU+A.c*A.loV) :
    A.c*A.loU-A.s*(A.loV+A.side)<1 := by
  have b := normal_bounds normal
  have hc : 0<A.c := by linarith only [b.1]
  have cross := mul_nonneg hc.le normal.1
  have width := mul_pos (sub_pos.mpr side)
    (show 0<1+A.c*A.s by linarith only [cross])
  have defect := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤1-A.s by linarith only [b.2.2.2.1])
  have floorWeight := mul_nonneg normal.1 (sub_nonneg.mpr floor)
  have identity :
      A.c*(1-(A.c*A.loU-A.s*(A.loV+A.side))) =
      (2*(A.c+A.s)-A.side-A.loU)+
      A.s*(A.s*A.loU+A.c*A.loV-1)+
      (A.side-1)*(1+A.c*A.s)+(1-A.c)*(1-A.s) := by
    linear_combination (-A.loU)*normal.2.2
  have scaled : 0<A.c*(1-(A.c*A.loU-A.s*(A.loV+A.side))) := by
    nlinarith only [identity,cap,floorWeight,width,defect]
  have gap := pos_of_mul_pos_right scaled hc.le
  linarith only [gap]

end N12Compact.PositiveCentralNegativeFloor
