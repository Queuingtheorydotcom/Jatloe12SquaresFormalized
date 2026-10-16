import Compact.Geometry.CentralWallEscape
import Compact.Geometry.ClosedPointExclusion
import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! An actual outer horizontal segment blocks the lower-U escape of a
positive right wall. The proof constructs a closed point on the wall's
upper V face at height three. The endpoint (3.5,3) is explicit: this
module does not assert that the original corner owns it. Source only. -/
namespace N12Compact.RightWallOuterSegment

open S12 S12Pilot FourSquareAnchors C977CornerCubic
set_option Elab.async false

private theorem affine_between {k b low high x a z : ℝ}
    (left : low<k*a+b ∧ k*a+b<high)
    (right : low<k*z+b ∧ k*z+b<high)
    (lower : a≤x) (upper : x≤z) : low<k*x+b ∧ k*x+b<high := by
  by_cases positive : 0≤k
  · have first := mul_nonneg positive (sub_nonneg.mpr lower)
    have last := mul_nonneg positive (sub_nonneg.mpr upper)
    constructor <;> nlinarith only [left.1,right.2,first,last]
  · have first := mul_nonneg (show 0≤-k by linarith only [positive])
      (sub_nonneg.mpr lower)
    have last := mul_nonneg (show 0≤-k by linarith only [positive])
      (sub_nonneg.mpr upper)
    constructor <;> nlinarith only [right.1,left.2,first,last]

private theorem row_segment (E : OpenSquare) (x : ℝ)
    (left : E.Inside (16/5) 3) (right : E.Inside (7/2) 3)
    (lower : 16/5≤x) (upper : x≤7/2) : E.Inside x 3 := by
  have u := affine_between ⟨left.1,left.2.1⟩ ⟨right.1,right.2.1⟩ lower upper
  have v := affine_between ⟨left.2.2.1,left.2.2.2⟩
    ⟨right.2.2.1,right.2.2.2⟩ lower upper
  exact ⟨u.1,u.2,v.1,v.2⟩

private theorem circle_margin {d t : ℝ} (normal : Normal d t) :
    1+d*t-t^2/2≤d+t := by
  have bounds := normal_bounds normal
  have twice : 1≤d+2*t := by
    linarith only [bounds.2.2.2.2.1,normal.1]
  have product := mul_nonneg (sq_nonneg t)
    (show 0≤d+2*t-1 by linarith only [twice])
  have identity :
      2*(1+d)*(d+t-1-d*t+t^2/2)=t^2*(d+2*t-1) := by
    linear_combination 2*(1-t)*normal.2.2
  have scaled : 0≤(1+d)*(d+t-1-d*t+t^2/2) := by
    linarith only [identity,product]
  have result := nonneg_of_mul_nonneg_right scaled
    (show 0<1+d by linarith only [bounds.1])
  linarith only [result]

/-- The genuine corner segment from 3.2 to 3.5 prevents a positive
right wall from placing its lower U face past (3,2). No orientation or
containment assumption on the foreign square is needed once its two
strict endpoints have been supplied. -/
theorem impossible (R E : OpenSquare) (normal : Normal R.c R.s)
    (side : 1<R.side) (box : InsideContainer R)
    (marker : R.Inside (1543/500) 2)
    (start : 3*R.c+2*R.s≤R.loU)
    (outward : E.Inside (16/5) 3) (farther : E.Inside (7/2) 3)
    (apart : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y)) : False := by
  classical
  have bounds := normal_bounds normal
  have cp : 0<R.c := by linarith only [bounds.1]
  have wall := CentralWallEscape.right_wall R box
  by_cases zero : R.s=0
  · have one : R.c=1 := by nlinarith only [normal.2.2,zero,cp]
    rw [zero,one] at wall start
    linarith only [wall,start,side]
  have sp : 0<R.s := lt_of_le_of_ne normal.1 (Ne.symm zero)
  have width : (1/5)*R.c+R.s<1 := by
    linarith only [normal.2.1,bounds.2.2.2.2.2]
  have cap : R.loV+R.side≤3*R.c-(16/5)*R.s := by
    apply le_of_not_gt
    intro high
    apply apart (16/5) 3
    refine ⟨outward,?_,?_,?_,by linarith only [high]⟩ <;>
      linarith only [marker.1,marker.2.2.1,start,side,width,cp,
        normal.1,normal.2.1]
  let H : ℝ := R.loV+R.side
  let X : ℝ := (3*R.c-H)/R.s
  have coordinate : R.s*X=3*R.c-H := by
    dsimp [X]
    field_simp [ne_of_gt sp]
  have rowV : -R.s*X+3*R.c=H := by linarith only [coordinate]
  have lowVertex : R.s*R.loU+R.c*H<3 := by
    have first := mul_lt_mul_of_pos_left marker.1 sp
    have last := mul_le_mul_of_nonneg_left cap cp.le
    have positive := mul_nonneg cp.le normal.1
    dsimp [H] at *
    nlinarith only [first,last,normal.2.2,sq_nonneg R.s,positive]
  have highVertex : 3<R.s*(R.loU+R.side)+R.c*H := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr wall)
    have last := mul_nonneg (sub_nonneg.mpr bounds.2.1)
      (sub_nonneg.mpr bounds.2.2.2.1)
    have excess := mul_pos (sub_pos.mpr side)
      (show 0<1+R.c*R.s by nlinarith only [mul_nonneg cp.le normal.1])
    have identity :
        R.s*(R.s*(R.loU+R.side)+R.c*H-3)=
        R.c*(4-R.c*(R.loU+R.side)+R.s*R.loV)+
        (R.loU-(3*R.c+2*R.s))+
        (R.side-1)*(1+R.c*R.s)+(1-R.c)*(1-R.s) := by
      dsimp [H]
      linear_combination (R.loU+R.side)*normal.2.2
    have product : 0<R.s*(R.s*(R.loU+R.side)+R.c*H-3) := by
      nlinarith only [identity,first,last,excess,start]
    have result := pos_of_mul_pos_right product sp.le
    linarith only [result]
  have rowU : R.s*(R.c*X+3*R.s)=3-R.c*H := by
    have scaled := congrArg (fun z : ℝ => R.c*z) coordinate
    clear_value X H
    linear_combination scaled + 3 * normal.2.2
  have closed : ClosedInside R X 3 := by
    have lower : R.loU≤R.c*X+3*R.s := by
      apply (mul_le_mul_iff_right₀ sp).mp
      linarith only [rowU,lowVertex]
    have upper : R.c*X+3*R.s≤R.loU+R.side := by
      apply (mul_le_mul_iff_right₀ sp).mp
      linarith only [rowU,highVertex]
    exact ⟨by linarith only [lower],by linarith only [upper],by dsimp [H] at rowV; linarith only [rowV,side],
      by dsimp [H] at rowV; linarith only [rowV]⟩
  have lowerX : 16/5≤X := by
    apply (mul_le_mul_iff_right₀ sp).mp
    dsimp [H] at coordinate
    linarith only [coordinate,cap]
  have upperX : X<7/2 := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr start)
    have excess := mul_pos (sub_pos.mpr side)
      (show 0<R.c+R.s by linarith only [cp,normal.1])
    have margin := circle_margin normal
    have product := congrArg (fun z : ℝ => R.s*z) coordinate
    have scaled : R.s^2*(X-7/2)<0 := by
      dsimp [H] at product
      nlinarith only [wall,first,excess,margin,product,normal.2.2]
    have result : X - 7/2 < 0 := by
      by_contra h
      have nonnegative := mul_nonneg (sq_nonneg R.s) (le_of_not_gt h)
      linarith only [scaled, nonnegative]
    linarith only [result]
  exact ClosedPointExclusion.outside_of_closed E R X 3 apart closed
    (row_segment E X outward farther lowerX upperX.le)

#print axioms impossible
end N12Compact.RightWallOuterSegment
