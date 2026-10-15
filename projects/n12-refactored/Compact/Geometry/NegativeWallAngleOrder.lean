import Compact.Geometry.CentralLeftWallNegative
import Compact.Geometry.PositiveCentralLeftBand

/-! A negative left wall separating from the positive central square must
have strictly larger sine magnitude. All comparisons are exact continuous
unit-normal inequalities. The still-unproved central point (1,2) remains
an explicit geometric premise in the final theorem. -/
namespace N12Compact.NegativeWallAngleOrder

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

private theorem central_bounds {C S : ℝ} (normal : Normal C S)
    (slope : 13*S≤7*C) : (7/8:ℝ)≤C ∧ S≤1/2 := by
  have b := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr slope)
    (show 0≤7*C+13*S by linarith only [b.1,normal.1])
  constructor
  · by_contra no
    have small := mul_nonneg
      (show 0≤7/8-C by linarith only [no])
      (show 0≤7/8+C by linarith only [b.1])
    nlinarith only [normal.2.2,product,small]
  · by_contra no
    have large := mul_pos
      (show 0<S-1/2 by linarith only [no])
      (show 0<S+1/2 by linarith only [normal.1])
    nlinarith only [normal.2.2,product,large]

private theorem ordered_normals {C S d t : ℝ}
    (an : Normal C S) (wn : Normal d t) (order : t≤S) :
    C≤d ∧ d*t≤C*S := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have squares := mul_nonneg (sub_nonneg.mpr order) (add_nonneg an.1 wn.1)
  have cosines : C≤d := by
    by_contra no
    have bad := mul_pos
      (show 0<C-d by linarith only [no])
      (show 0<C+d by linarith only [ab.1,wb.1])
    nlinarith only [bad,squares,an.2.2,wn.2.2]
  have remaining : 0≤1-S^2-t^2 := by
    have bound := mul_nonneg (show 0≤C-t by linarith only [order,an.2.1])
      (show 0≤C+t by linarith only [ab.1,wn.1])
    nlinarith only [bound,an.2.2]
  have product := mul_nonneg
    (show 0≤S^2-t^2 by nlinarith only [squares]) remaining
  have identity : (C*S)^2-(d*t)^2=(S^2-t^2)*(1-S^2-t^2) := by
    linear_combination S^2*an.2.2-t^2*wn.2.2
  have cs := mul_nonneg (show 0≤C by linarith only [ab.1]) an.1
  have dt := mul_nonneg (show 0≤d by linarith only [wb.1]) wn.1
  have products : d*t≤C*S := by
    by_contra no
    have bad := mul_pos
      (show 0<d*t-C*S by linarith only [no])
      (show 0<d*t+C*S by linarith only [no,cs])
    nlinarith only [identity,product,bad]
  exact ⟨cosines,products⟩

private def H (d t : ℝ) : ℝ := (1-d)*(1-t)-(43/500)*t^2

/-- This chord calculation replaces a derivative argument for H. -/
private theorem h_order {C S d t : ℝ}
    (an : Normal C S) (wn : Normal d t) (small : S≤1/2) (order : t≤S) :
    H d t≤H C S := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have coefficient : (41/125:ℝ)≤1-S-(43/500)*(d+C) := by
    linarith only [small,ab.2.1,wb.2.1]
  have weighted := mul_nonneg (add_nonneg an.1 wn.1)
    (sub_nonneg.mpr coefficient)
  have defect := mul_nonneg (sub_nonneg.mpr wb.2.1) (sub_nonneg.mpr ab.2.1)
  have smallSquare := mul_nonneg wn.1
    (show 0≤1/2-t by linarith only [order,small])
  have numerator : 0≤(S+t)*(1-S-(43/500)*(d+C))-(1-d)*(d+C) := by
    nlinarith only [weighted,defect,smallSquare,order,wn.1,wn.2.2]
  have product := mul_nonneg (sub_nonneg.mpr order) numerator
  have identity :
      (d+C)*(H C S-H d t) =
        (S-t)*((S+t)*(1-S-(43/500)*(d+C))-(1-d)*(d+C)) := by
    unfold H
    linear_combination (1-S)*wn.2.2-(1-S)*an.2.2
  by_contra no
  have bad := mul_neg_of_pos_of_neg
    (show 0<d+C by linarith only [ab.1,wb.1])
    (show H C S-H d t<0 by linarith only [no])
  nlinarith only [bad,product,identity]

/-- At equal tilts the remainder is a sum of nonnegative factors. -/
private theorem equal_order {C S : ℝ} (normal : Normal C S) (large : (7/8:ℝ)≤C) :
    0≤(1-C)*C*(C^2-S^2)-H C S := by
  have b := normal_bounds normal
  have cross : 0≤1-2*C*S := by nlinarith only [normal.2.2,sq_nonneg (C-S)]
  have first := mul_nonneg (mul_nonneg (sub_nonneg.mpr b.2.1) normal.1) cross
  have second := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤(543/500)*C-457/500 by linarith only [large])
  have identity :
      (1-C)*C*(C^2-S^2)-H C S =
        (1-C)*S*(1-2*C*S)+(1-C)*((543/500)*C-457/500) := by
    unfold H
    linear_combination ((1-C)*C+43/500)*normal.2.2
  nlinarith only [first,second,identity]

theorem scalar {C S d t : ℝ} (an : Normal C S) (wn : Normal d t)
    (slope : 13*S≤7*C) (order : t≤S) :
    0≤(1-C)*d*(C*d-S*t)-(1-d)*(1-t)+(43/500)*t^2 := by
  have bounds := central_bounds an slope
  have angles := ordered_normals an wn order
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have squared := mul_nonneg (sub_nonneg.mpr angles.1)
    (show 0≤d+C by linarith only [ab.1,wb.1])
  have first := mul_nonneg (show 0≤C by linarith only [ab.1]) squared
  have second := mul_nonneg an.1 (sub_nonneg.mpr angles.2)
  have support : C*(C^2-S^2)≤d*(C*d-S*t) := by
    nlinarith only [first,second]
  have scaled := mul_nonneg (sub_nonneg.mpr ab.2.1) (sub_nonneg.mpr support)
  have monotone := h_order an wn bounds.2 order
  have endpoint := equal_order an bounds.1
  unfold H at monotone endpoint
  nlinarith only [scaled,monotone,endpoint]

/-- The true W-U separator, actual left-wall coupling and upper-V cap
force the wall tilt to exceed the central tilt. -/
theorem support_order (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (same : A.side=W.side) (side : 1<A.side)
    (slope : 13*A.s≤7*A.c)
    (cap : A.loU+A.side≤2*(A.c+A.s)) (west : A.Inside 1 2)
    (top : W.loV+W.side≤(457/500)*t+3*W.c)
    (wall : W.side*(W.c+t)≤W.c*(W.loU+W.side)+t*(W.loV+W.side))
    (sep : W.loU+W.side≤lower A W.c W.s) : A.s<t := by
  have ab := normal_bounds an
  have wb := normal_bounds wn
  have ac : 0<A.c := by linarith only [ab.1]
  have dc : 0<W.c := by linarith only [wb.1]
  let k := A.c*W.c-A.s*t
  let h := A.s*W.c+A.c*t
  have kp : 0≤k := by
    have first := mul_nonneg dc.le (sub_nonneg.mpr an.2.1)
    have second := mul_nonneg an.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,second]
  have hp : 0≤h := by
    dsimp [h]
    exact add_nonneg (mul_nonneg an.1 dc.le) (mul_nonneg ac.le wn.1)
  have form : lower A W.c W.s=k*A.loU-h*(A.loV+A.side) := by
    rw [lower_in_bands,ws]
    have ku : W.c*A.c+(-t)*A.s=k := by dsimp [k]; ring
    have hv : -W.c*A.s+(-t)*A.c=-h := by dsimp [h]; ring
    rw [ku,hv,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  rw [form] at sep
  have up := mul_nonneg kp (sub_nonneg.mpr cap)
  have vp := mul_nonneg hp (sub_nonneg.mpr west.2.2.2.le)
  have bound : W.loU+W.side≤
      k*(2*(A.c+A.s)-A.side)-h*(2*A.c-A.s) := by
    nlinarith only [sep,up,vp]
  have weighted := mul_nonneg dc.le (sub_nonneg.mpr bound)
  have weightedTop := mul_nonneg wn.1 (sub_nonneg.mpr top)
  let M := W.c+t+W.c*k
  let R := W.c*(2*k*(A.c+A.s)-h*(2*A.c-A.s))+
    (457/500)*t^2+3*W.c*t
  have mp : 0<M := by
    have product := mul_nonneg dc.le kp
    dsimp [M]
    linarith only [dc,wn.1,product]
  have combined : A.side*M≤R := by
    rw [←same] at wall weighted weightedTop
    dsimp [M,R]
    nlinarith only [wall,weighted,weightedTop]
  have width := mul_pos (sub_pos.mpr side) mp
  have identity :
      (1-A.c)*W.c*(A.c*W.c-A.s*t)-(1-W.c)*(1-t)+(43/500)*t^2=M-R := by
    dsimp [M,R,k,h]
    linear_combination (W.c^2-2*W.c*t)*an.2.2+wn.2.2
  by_contra no
  have nonnegative := scalar an wn slope (le_of_not_gt no)
  nlinarith only [combined,width,identity,nonnegative]

/-- Original local geometry supplies every support and angle premise.
The left point (1,2) is explicit; this theorem does not prove that point. -/
theorem angle_order (A W : OpenSquare) (t : ℝ)
    (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (same : A.side=W.side) (side : 1<A.side) (sideCap : A.side≤1001/1000)
    (centerCap : A.loU+A.side≤2*(A.c+A.s))
    (west : A.Inside 1 2) (aLeft : A.Inside (3/2) 2) (low : A.Inside 2 (3/2))
    (missingNW : ¬A.Inside (33/20) (47/20))
    (foreignLow : ¬A.Inside 1 (8/5))
    (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (point : W.Inside 1 (113/50))
    (missingTop : ¬W.Inside (457/500) 3)
    (missingFar : ¬W.Inside (19/25) (187/100))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y)) : A.s<t := by
  have sideW : 1<W.side := by rwa [←same]
  have ab := normal_bounds an
  have north := PositiveCentralLeftBand.northwest_cap A side
    (by linarith only [ab.1]) an.1 an.2.1 aLeft low missingNW foreignLow
  have slope := PositiveCentralLeftBand.left_point_tilt A north west
  have missing : ¬W.Inside 1 2 := fun w => apart 1 2 ⟨west,w⟩
  obtain ⟨_,top,wall⟩ := LeftWallNegativeFaces.faces W t ws wn sideW box
    marker point missing missingTop
  have sep := CentralLeftWallNegative.wall_axis A W t an wn ws same sideW sideCap
    west low box marker point missingTop missingFar apart
  exact support_order A W t an wn ws same side slope.le centerCap west top wall sep

end N12Compact.NegativeWallAngleOrder
