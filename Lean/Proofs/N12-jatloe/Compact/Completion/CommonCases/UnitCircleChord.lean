import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! Exact chord interpolation and linear-support monotonicity on the
closed first-quadrant unit arc. No angular parameter, derivative or
nondegeneracy of a coordinate endpoint is required. -/
namespace N12Compact.CommonCases.UnitCircleChord
set_option Elab.async false

theorem cosine_order {c s d t : ℝ} (cn : 0≤c) (dn : 0≤d)
    (cu : c^2+s^2=1) (du : d^2+t^2=1)
    (sn : 0≤s) (tn : 0≤t) (order : s≤t) : d≤c := by
  apply le_of_not_gt
  intro bad
  have first := mul_pos (sub_pos.mpr bad) (show 0<d+c by linarith only [bad,cn])
  have last := mul_nonneg (sub_nonneg.mpr order) (add_nonneg tn sn)
  nlinarith only [first,last,cu,du]

theorem cross_order {c s d t : ℝ} (cn : 0≤c) (dn : 0≤d)
    (cu : c^2+s^2=1) (du : d^2+t^2=1)
    (sn : 0≤s) (tn : 0≤t) (order : s≤t) : 0≤c*t-s*d := by
  have cosine := cosine_order cn dn cu du sn tn order
  have first := mul_nonneg cn (sub_nonneg.mpr order)
  have last := mul_nonneg sn (sub_nonneg.mpr cosine)
  nlinarith only [first,last]

theorem linear_nonnegative {c s d t h r b A B : ℝ}
    (cn : 0≤c) (dn : 0≤d) (hn : 0≤h)
    (cu : c^2+s^2=1) (du : d^2+t^2=1) (hu : h^2+r^2=1)
    (left : s≤r) (right : r≤t) (An : 0≤A)
    (first : 0≤b+A*c+B*s) (last : 0≤b+A*d+B*t) :
    0≤b+A*h+B*r := by
  by_cases same : s=t
  · have rs : r=s := by linarith only [left,right,same]
    have hc : h=c := by
      apply le_antisymm
      · apply le_of_not_gt; intro bad
        have product := mul_pos (sub_pos.mpr bad)
          (show 0<h+c by linarith only [bad,cn])
        rw [rs] at hu
        nlinarith only [product,hu,cu]
      · apply le_of_not_gt; intro bad
        have product := mul_pos (sub_pos.mpr bad)
          (show 0<c+h by linarith only [bad,hn])
        rw [rs] at hu
        nlinarith only [product,hu,cu]
    simpa only [hc,rs] using first
  have gap : 0<t-s := by
    apply lt_of_le_of_ne (sub_nonneg.mpr (left.trans right))
    intro h
    exact same (by linarith only [h])
  let T := (t-r)*c+(r-s)*d
  have Tn : 0≤T := add_nonneg
    (mul_nonneg (sub_nonneg.mpr right) cn)
    (mul_nonneg (sub_nonneg.mpr left) dn)
  have product := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr left) (sub_nonneg.mpr right))
    (add_nonneg (sq_nonneg (c-d)) (sq_nonneg (t-s)))
  have identity : (t-s)^2*h^2-T^2=
      (r-s)*(t-r)*((c-d)^2+(t-s)^2) := by
    dsimp [T]
    linear_combination (t-s)^2*hu-(t-r)*(t-s)*cu-(r-s)*(t-s)*du
  have chord : T≤(t-s)*h := by
    apply le_of_not_gt
    intro bad
    have last := mul_pos (show 0<T-(t-s)*h by linarith only [bad])
      (show 0<T+(t-s)*h by
        have p := mul_nonneg gap.le hn
        linarith only [bad,p])
    nlinarith only [last,identity,product]
  have f0 := mul_nonneg (sub_nonneg.mpr right) first
  have f1 := mul_nonneg (sub_nonneg.mpr left) last
  have correction := mul_nonneg An (sub_nonneg.mpr chord)
  have weighted : 0≤(t-s)*(b+A*h+B*r) := by
    dsimp [T] at correction
    nlinarith only [f0,f1,correction]
  exact nonneg_of_mul_nonneg_right weighted gap

/-- An increasing linear support up to its upper endpoint. -/
theorem increasing {c s d t A B : ℝ} (cp : 0<c) (dn : 0≤d)
    (cu : c^2+s^2=1) (du : d^2+t^2=1)
    (sn : 0≤s) (tn : 0≤t) (order : t≤s)
    (An : 0≤A) (Bn : 0≤B) (derivative : 0≤B*c-A*s) :
    A*d+B*t≤A*c+B*s := by
  have cosine := cosine_order dn cp.le du cu tn sn order
  have first := mul_nonneg Bn (sub_nonneg.mpr cosine)
  have last := mul_nonneg An (sub_nonneg.mpr order)
  have bracket : 0≤B*(c+d)-A*(s+t) := by
    nlinarith only [first,last,derivative]
  have product := mul_nonneg (sub_nonneg.mpr order) bracket
  have identity : (c+d)*((A*c+B*s)-(A*d+B*t))=
      (s-t)*(B*(c+d)-A*(s+t)) := by
    linear_combination A*cu-A*du
  have weighted : 0≤(c+d)*((A*c+B*s)-(A*d+B*t)) := by
    rw [identity]; exact product
  have result := nonneg_of_mul_nonneg_right weighted (show 0<c+d by linarith only [cp,dn])
  linarith only [result]

/-- A decreasing linear support beyond its lower endpoint. -/
theorem decreasing {c s d t A B : ℝ} (cp : 0<c) (dn : 0≤d)
    (cu : c^2+s^2=1) (du : d^2+t^2=1)
    (sn : 0≤s) (tn : 0≤t) (order : s≤t)
    (An : 0≤A) (Bn : 0≤B) (derivative : 0≤A*s-B*c) :
    A*d+B*t≤A*c+B*s := by
  have cosine := cosine_order cp.le dn cu du sn tn order
  have first := mul_nonneg An (sub_nonneg.mpr order)
  have last := mul_nonneg Bn (sub_nonneg.mpr cosine)
  have bracket : 0≤A*(s+t)-B*(c+d) := by
    nlinarith only [first,last,derivative]
  have product := mul_nonneg (sub_nonneg.mpr order) bracket
  have identity : (c+d)*((A*c+B*s)-(A*d+B*t))=
      (t-s)*(A*(s+t)-B*(c+d)) := by
    linear_combination A*cu-A*du
  have weighted : 0≤(c+d)*((A*c+B*s)-(A*d+B*t)) := by
    rw [identity]; exact product
  have result := nonneg_of_mul_nonneg_right weighted (show 0<c+d by linarith only [cp,dn])
  linarith only [result]

end N12Compact.CommonCases.UnitCircleChord
