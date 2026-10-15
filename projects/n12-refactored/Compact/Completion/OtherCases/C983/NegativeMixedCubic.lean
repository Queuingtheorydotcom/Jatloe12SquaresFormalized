import Compact.Completion.C981.HalfAngle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Positivity

/-! C581 §7: the ordered mixed-angle numerator is a cubic in `z-w`.
Monotonicity of its four coefficients reduces the whole closed triangle
to one cubic with four positive Bernstein coefficients. No sampled angles
or generated degree-seven certificate enter this argument. -/
namespace N12Compact.Completion.OtherCases.C983.NegativeMixedCubic
open Set
set_option Elab.async false

def numerator (z w : ℝ) : ℝ :=
  4*w*z*(1+w^2)*(1+z^2) -
  ((1-w^2)*(1-z^2)+4*w*z)*(1-2*w+3*w^2)*(1+z) +
  (1-z^2)*(1-w)^2*(1+w^2)*(1+z)

private def A0 (w : ℝ) : ℝ := w^3*(1-w)*(1+w^2)
private def A1 (w : ℝ) : ℝ := w^2*(4-3*w)*(1+w^2)
private def A2 (w : ℝ) : ℝ := -3*w^4+5*w^3-2*w^2+5*w-1
private def A3 (w : ℝ) : ℝ := 1+2*w^2-w^3
private def cubic (w y : ℝ) : ℝ := A0 w+A1 w*y+A2 w*y^2+A3 w*y^3

private theorem derivative0 (w : ℝ) :
    HasDerivAt A0 (w^2*(3-4*w+5*w^2-6*w^3)) w := by
  have d := hasDerivAt_id w
  have result := ((d.pow 3).mul ((hasDerivAt_const w 1).sub d)).mul
    ((hasDerivAt_const w 1).add (d.pow 2))
  convert result using 1 <;> dsimp only [A0] <;> ring

private theorem derivative1 (w : ℝ) :
    HasDerivAt A1 (w*(8-9*w+16*w^2-15*w^3)) w := by
  have d := hasDerivAt_id w
  have result := ((d.pow 2).mul ((hasDerivAt_const w 4).sub (d.const_mul 3))).mul
    ((hasDerivAt_const w 1).add (d.pow 2))
  convert result using 1 <;> dsimp only [A1] <;> ring

private theorem derivative2 (w : ℝ) :
    HasDerivAt A2 (5-4*w+15*w^2-12*w^3) w := by
  have d := hasDerivAt_id w
  have result := (((((d.pow 4).const_mul (-3)).add ((d.pow 3).const_mul 5)).sub
    ((d.pow 2).const_mul 2)).add (d.const_mul 5)).sub_const 1
  convert result using 1 <;> dsimp only [A2] <;> ring

private theorem derivative3 (w : ℝ) :
    HasDerivAt A3 (w*(4-3*w)) w := by
  have d := hasDerivAt_id w
  have result := ((hasDerivAt_const w 1).add ((d.pow 2).const_mul 2)).sub (d.pow 3)
  convert result using 1 <;> dsimp only [A3] <;> ring

/-- The four strictly positive derivative factors from equation (37). -/
private theorem derivative_bounds (w : ℝ) (lo : 1/9≤w) (hi : w≤2/7) :
    589/343≤3-4*w+5*w^2-6*w^3 ∧
    1742/343≤8-9*w+16*w^2-15*w^3 ∧
    1227/343≤5-4*w+15*w^2-12*w^3 ∧ 22/7≤4-3*w := by
  have wn : 0≤w := by linarith only [lo]
  have cube : w^3≤8/343 := by
    have weight := mul_nonneg (sub_nonneg.mpr hi)
      (show 0≤w^2+(2/7)*w+4/49 by positivity)
    nlinarith only [weight]
  exact ⟨by nlinarith only [hi,cube,sq_nonneg w],
    by nlinarith only [hi,cube,sq_nonneg w],
    by nlinarith only [hi,cube,sq_nonneg w], by linarith only [hi]⟩

private theorem coefficient_monotone (f df : ℝ → ℝ)
    (derivative : ∀ w,HasDerivAt f (df w) w)
    (nonnegative : ∀ w,1/9≤w → w≤2/7 → 0≤df w) :
    MonotoneOn f (Icc (1/9) (2/7)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro w _
    exact (derivative w).continuousAt.continuousWithinAt
  · intro w _
    exact (derivative w).differentiableAt.differentiableWithinAt
  · intro w hw
    have interval := interior_subset hw
    rw [(derivative w).deriv]
    exact nonnegative w interval.1 interval.2

private theorem coefficients_lower (w : ℝ) (lo : 1/9≤w) (hi : w≤2/7) :
    A0 (1/9)≤A0 w ∧ A1 (1/9)≤A1 w ∧
      A2 (1/9)≤A2 w ∧ A3 (1/9)≤A3 w := by
  have left : (1/9 : ℝ)∈Icc (1/9) (2/7) := by norm_num
  have right : w∈Icc (1/9) (2/7) := ⟨lo,hi⟩
  have m0 := coefficient_monotone A0 _ derivative0 (by
    intro x hx hy
    have bound := (derivative_bounds x hx hy).1
    exact mul_nonneg (sq_nonneg x) (by linarith only [bound]))
  have m1 := coefficient_monotone A1 _ derivative1 (by
    intro x hx hy
    have bound := (derivative_bounds x hx hy).2.1
    exact mul_nonneg (by linarith only [hx]) (by linarith only [bound]))
  have m2 := coefficient_monotone A2 _ derivative2 (by
    intro x hx hy
    have bound := (derivative_bounds x hx hy).2.2.1
    linarith only [bound])
  have m3 := coefficient_monotone A3 _ derivative3 (by
    intro x hx hy
    have bound := (derivative_bounds x hx hy).2.2.2
    exact mul_nonneg (by linarith only [hx]) (by linarith only [bound]))
  exact ⟨m0 left right lo,m1 left right lo,m2 left right lo,m3 left right lo⟩

private theorem cubic_lower (w y : ℝ) (lo : 1/9≤w) (hi : w≤2/7)
    (yn : 0≤y) : cubic (1/9) y≤cubic w y := by
  obtain ⟨a0,a1,a2,a3⟩ := coefficients_lower w lo hi
  exact add_le_add (add_le_add (add_le_add a0
    (mul_le_mul_of_nonneg_right a1 yn))
      (mul_le_mul_of_nonneg_right a2 (sq_nonneg y)))
        (mul_le_mul_of_nonneg_right a3 (pow_nonneg yn 3))

/-- Subtracting the smallest Bernstein coefficient also subtracts that
constant times the partition of unity. Each remaining coefficient is
nonnegative, including the zero last coefficient. -/
private theorem left_edge (y : ℝ) (lo : 0≤y) (hi : y≤11/63) :
    16/27783≤cubic (1/9) y := by
  let eta := (63/11 : ℝ)*y
  have en : 0≤eta := by dsimp only [eta]; positivity
  have eh : eta≤1 := by dsimp only [eta]; linarith only [hi]
  have one : 0≤1-eta := sub_nonneg.mpr eh
  have b0 : (0 : ℝ)≤656/531441-16/27783 := by norm_num
  have b1 : (0 : ℝ)≤4838/1240029-16/27783 := by norm_num
  have b2 : (0 : ℝ)≤200/107163-16/27783 := by norm_num
  have nonnegative : 0≤(656/531441-16/27783)*(1-eta)^3+
      (4838/1240029-16/27783)*(3*eta*(1-eta)^2)+
      (200/107163-16/27783)*(3*eta^2*(1-eta)) := by positivity
  have identity : cubic (1/9) y-16/27783=
      (656/531441-16/27783)*(1-eta)^3+
      (4838/1240029-16/27783)*(3*eta*(1-eta)^2)+
      (200/107163-16/27783)*(3*eta^2*(1-eta)) := by
    dsimp only [cubic,A0,A1,A2,A3,eta]
    ring
  linarith only [identity,nonnegative]

/-- The exact stronger margin (44) on the entire closed angle triangle. -/
theorem triangle_margin (z w : ℝ) (lo : 1/9≤w) (order : w≤z)
    (hi : z≤2/7) : 64/250047≤numerator z w := by
  have wh : w≤2/7 := le_trans order hi
  have yn : 0≤z-w := sub_nonneg.mpr order
  have yh : z-w≤11/63 := by linarith only [lo,hi]
  have lower := le_trans (left_edge (z-w) yn yh) (cubic_lower w (z-w) lo wh yn)
  have weight := mul_nonneg (sub_nonneg.mpr lo)
    (show 0≤cubic w (z-w) by linarith only [lower])
  have identity : numerator z w=4*w*cubic w (z-w) := by
    dsimp only [numerator,cubic,A0,A1,A2,A3]
    ring
  nlinarith only [identity,lower,weight]

theorem triangle (z w : ℝ) (lo : 1/9≤w) (order : w≤z) (hi : z≤2/7) :
    0≤numerator z w := le_trans (by norm_num) (triangle_margin z w lo order hi)

#print axioms triangle_margin
end N12Compact.Completion.OtherCases.C983.NegativeMixedCubic
