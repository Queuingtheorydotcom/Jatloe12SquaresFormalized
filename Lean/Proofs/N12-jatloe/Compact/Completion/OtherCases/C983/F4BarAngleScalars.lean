import Compact.Completion.OtherCases.C983.F4MergedCenterMonotone
import Compact.Completion.C981.HalfAngle

/-! The written one-variable estimates in C983-F4-BAR-ANGLE-REDUCTION,
Theorem 1. The derivative is the displayed J' from that proof. -/
namespace N12Compact.Completion.OtherCases.C983.F4BarAngleScalars
open Set
set_option Elab.async false
noncomputable section

theorem slope (c s : ℝ) (cp : 0<c) (sn : 0≤s) (unit : c^2+s^2=1)
    (width : 1<(4/5)*c+(37/50)*s) : c/3<s := by
  apply lt_of_not_ge
  intro small
  have first : 0≤c-3*s := by linarith only [small]
  have second : 0≤(8649/2500)*c-(3653/2500)*s := by linarith only [small,cp]
  have product := mul_nonneg first second
  have identity : (157/50)^2*(c^2+s^2)-10*((4/5)*c+(37/50)*s)^2=
      (c-3*s)*((8649/2500)*c-(3653/2500)*s) := by ring
  have square := mul_pos (show 0<(4/5)*c+(37/50)*s-1 by linarith only [width])
    (show 0<(4/5)*c+(37/50)*s+1 by linarith only [cp,sn])
  rw [unit] at identity
  nlinarith only [product,identity,square]

def J (alpha beta q : ℝ) : ℝ := Real.cos q+Real.sin q-1-
  alpha*Real.cos q*Real.sin q-beta*(Real.cos q)^2+(13/50)*(Real.sin q)^2

private theorem derivative (alpha beta q : ℝ) :
    HasDerivAt (J alpha beta)
      ((Real.cos q-Real.sin q)*(1-alpha*(Real.cos q+Real.sin q))+
        2*(beta+13/50)*Real.cos q*Real.sin q) q := by
  have result := (((((Real.hasDerivAt_cos q).add (Real.hasDerivAt_sin q)).sub_const 1).sub
    (((Real.hasDerivAt_cos q).mul (Real.hasDerivAt_sin q)).const_mul alpha)).sub
      (((Real.hasDerivAt_cos q).pow 2).const_mul beta)).add
        (((Real.hasDerivAt_sin q).pow 2).const_mul (13/50))
  convert result using 1
  · funext x
    simp only [J, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · ring

private theorem monotone (alpha beta : ℝ) (an : 0≤alpha) (ahi : alpha≤21/40)
    (bn : 0≤beta) : MonotoneOn (J alpha beta) (Icc 0 (Real.pi/4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · intro q _
    exact (derivative alpha beta q).continuousAt.continuousWithinAt
  · intro q _
    exact (derivative alpha beta q).differentiableAt.differentiableWithinAt
  · intro q hq
    have interval := interior_subset hq
    have pp := Real.pi_pos
    have cp := Real.cos_pos_of_mem_Ioo
      (show q∈Ioo (-(Real.pi/2)) (Real.pi/2) by
        constructor <;> linarith only [interval.1,interval.2,pp])
    have sn := Real.sin_nonneg_of_nonneg_of_le_pi interval.1
      (by linarith only [interval.2,pp])
    have order := Real.cos_le_cos_of_nonneg_of_le_pi interval.1
      (show Real.pi/2-q≤Real.pi by linarith only [interval.1,pp])
      (show q≤Real.pi/2-q by linarith only [interval.2])
    rw [Real.cos_pi_div_two_sub] at order
    have sum : Real.cos q+Real.sin q≤3/2 := by
      nlinarith only [Real.sin_sq_add_cos_sq q,sq_nonneg (Real.cos q-Real.sin q)]
    have bound := mul_nonneg an (sub_nonneg.mpr sum)
    have last : 0≤1-alpha*(Real.cos q+Real.sin q) := by nlinarith only [bound,ahi]
    rw [(derivative alpha beta q).deriv]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr order) last)
      (by positivity)

/-- Equations (9)--(10), including the exact endpoint 4/sqrt(10)>1.244. -/
theorem vertex_gap (c s alpha beta : ℝ) (cp : 0<c) (sn : 0≤s)
    (order : s≤c) (unit : c^2+s^2=1) (steep : c/3<s)
    (an : 0≤alpha) (ahi : alpha≤21/40) (bn : 0≤beta)
    (balance : alpha+3*beta=9/10) :
    0<c+s-1-alpha*c*s-beta*c^2+(13/50)*s^2 := by
  let z : ℝ := Real.sqrt (1/10)
  have zp : 0<z := Real.sqrt_pos.2 (by norm_num)
  have zs : z^2=1/10 := Real.sq_sqrt (by norm_num)
  obtain ⟨qBounds,cosq,sinq⟩ := F4MergedCenter.canonical_angle c s cp sn order unit
  obtain ⟨pBounds,cosp,sinp⟩ := F4MergedCenter.canonical_angle (3*z) z
    (by positivity) zp.le (by linarith only [zp]) (by nlinarith only [zs])
  have ratio : z/(3*z)≤s/c := by
    have first : z/(3*z)=(1/3 : ℝ) := by field_simp [zp.ne']
    rw [first]
    exact (le_div_iff₀ cp).mpr (by linarith only [steep])
  have angles := Real.arctan_mono ratio
  have compare := monotone alpha beta an ahi bn pBounds qBounds angles
  have endpoint : 0<J alpha beta (Real.arctan (z/(3*z))) := by
    rw [J,cosp,sinp]
    have weighted := congrArg (fun x : ℝ => 3*z^2*x) balance
    have gap : 311/250<4*z := by nlinarith only [zs,zp]
    nlinarith only [weighted,zs,gap]
  have result := lt_of_lt_of_le endpoint compare
  simpa only [J,cosq,sinq] using result

/-- The decreasing width at the rational half-angle 3/20. -/
theorem half (c s alpha beta : ℝ) (cp : 0<c) (sn : 0≤s)
    (order : s≤c) (unit : c^2+s^2=1)
    (parameters : (alpha=21/40 ∧ beta=1/8) ∨ (alpha=21/50 ∧ beta=4/25))
    (width : 1<(1+beta)*c+(alpha-4/5)*s) : s/(1+c)<3/20 := by
  have data := C981CompletionHalfAngle.data c s cp.le sn order unit
  let z := C981CompletionHalfAngle.half c s
  have zp : 0<1+z^2 := by positivity
  have scaled := mul_pos zp (sub_pos.mpr width)
  have identity : (1+z^2)*((1+beta)*c+(alpha-4/5)*s-1)=
      beta-(2+beta)*z^2+2*(alpha-4/5)*z := by
    calc
      _ = (1+beta)*((1+z^2)*c)+(alpha-4/5)*((1+z^2)*s)-(1+z^2) := by ring
      _ = _ := by rw [data.2.2.2.1,data.2.2.2.2]; ring
  change z<3/20
  apply lt_of_not_ge
  intro bad
  have squares := mul_nonneg (show 0≤z-3/20 by linarith only [bad])
    (show 0≤z+3/20 by linarith only [bad])
  rcases parameters with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    nlinarith only [scaled,identity,bad,squares]

end
end N12Compact.Completion.OtherCases.C983.F4BarAngleScalars
