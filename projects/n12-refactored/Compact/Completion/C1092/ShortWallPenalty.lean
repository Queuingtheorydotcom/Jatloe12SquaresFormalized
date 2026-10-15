import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! The sharp top-wall penalty over the full first-quadrant wall arc.
The two actual relative-angle orders meet at equality. A weighted chord
argument proves each complete arc; no orientation grid is used. -/
namespace N12Compact.C1092ShortWallPenalty
open C977CornerCubic
set_option Elab.async false

private theorem lower_arc (c s r t A B L : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (cn : c^2+s^2=1)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (rn : r^2+t^2=1)
    (order : c*t-s*r ≤ 0) (hL : 0 ≤ L)
    (axis : L ≤ A) (endpoint : L ≤ A*c+B*s) :
    L ≤ A*r+B*t := by
  classical
  by_cases zero : s=0
  · have c1 : c=1 := by nlinarith only [cn,zero,hc]
    have bound : t ≤ 0 := by
      simpa only [c1,zero,one_mul,zero_mul,sub_zero] using order
    have t0 : t=0 := le_antisymm bound ht
    have r1 : r=1 := by nlinarith only [rn,t0,hr]
    simpa only [r1,t0,mul_one,mul_zero,add_zero] using axis
  have sp : 0 < s := lt_of_le_of_ne hs (Ne.symm zero)
  have products := mul_nonneg (show 0 ≤ s*r-c*t by linarith only [order])
    (add_nonneg (mul_nonneg hs hr) (mul_nonneg hc ht))
  have squares : (s*r)^2-(c*t)^2=s^2-t^2 := by
    linear_combination s^2*rn-t^2*cn
  have tilt : t ≤ s := by
    nlinarith only [squares,products,hs,ht]
  have bracket : 0 ≤ s*(1+r)-t*(1+c) := by
    linarith only [order,tilt]
  have product := mul_nonneg (mul_nonneg hs ht) bracket
  have identity : (1+c)*(1+r)*(s*(r-1)+(1-c)*t) =
      s*t*(s*(1+r)-t*(1+c)) := by
    linear_combination s*(1+c)*rn-t*(1+r)*cn
  have scaled : 0 ≤ (1+c)*(1+r)*(s*(r-1)+(1-c)*t) := by
    linarith only [product,identity]
  have chord : 0 ≤ s*(r-1)+(1-c)*t := by
    apply nonneg_of_mul_nonneg_right scaled
    exact mul_pos (by linarith only [hc]) (by linarith only [hr])
  have first := mul_nonneg (show 0 ≤ s*r-c*t by linarith only [order])
    (sub_nonneg.mpr axis)
  have last := mul_nonneg ht (sub_nonneg.mpr endpoint)
  have correction := mul_nonneg hL chord
  have weighted : 0 ≤ s*(A*r+B*t-L) := by
    nlinarith only [first,last,correction]
  have result := nonneg_of_mul_nonneg_right weighted sp
  linarith only [result]

/-- Exact inequality (2) of the retained short-wall scalar appendix.
The physical top-wall normal may have either component greater. -/
theorem penalty {c s r t : ℝ} (cn : Normal c s)
    (hr : 0 ≤ r) (ht : 0 ≤ t) (rn : r^2+t^2=1) :
    1+c^2+c*s ≤ 2*c*r+c*t+s*t+|c*t-s*r| := by
  have cb := normal_bounds cn
  have hc : 0 ≤ c := by linarith only [cb.1]
  have hL : 0 ≤ 1+c^2+c*s := by
    nlinarith only [sq_nonneg c,mul_nonneg hc cn.1]
  have difference := mul_nonneg (sub_nonneg.mpr cb.2.1)
    (show 0 ≤ c+s-1 by linarith only [cb.2.2.2.2.1])
  have axis : 1+c^2+c*s ≤ 2*c+s := by
    nlinarith only [difference,cn.2.2]
  by_cases order : c*t-s*r ≤ 0
  · rw [abs_of_nonpos order]
    have result := lower_arc c s r t (2*c+s) s (1+c^2+c*s)
      hc cn.1 cn.2.2 hr ht rn order hL axis
      (by nlinarith only [cn.2.2])
    nlinarith only [result]
  · have reverse : s*r-c*t ≤ 0 := by linarith only [order]
    rw [abs_of_nonneg (by linarith only [order] : 0 ≤ c*t-s*r)]
    have result := lower_arc s c t r (2*c+s) (2*c-s) (1+c^2+c*s)
      cn.1 hc (by nlinarith only [cn.2.2]) ht hr
      (by nlinarith only [rn]) reverse hL axis
      (by nlinarith only [cn.2.2])
    nlinarith only [result]

#print axioms penalty
end N12Compact.C1092ShortWallPenalty
