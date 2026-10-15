import Compact.Completion.C1092.MMMP.OuterArmScalars

/-! The two wall-axis margins in INWARD-EXTENDED-ANCHOR-CENTER §§5.1–5.2.
The existing exact arc-interpolation and quadratic-monotonicity lemmas
apply to these coefficients. This avoids adding an analytic sine lemma.
Only the source translation is recorded here; it has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousAnchorScalars
open C977CornerCubic
set_option Elab.async false

theorem first {c s h b : ℝ} (cn : Normal c s) (sp : 0<s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) :
    0≤1/2+h^2/2+h*b/2+h*(c^2-(2/5)*c*s+s-2)+
      b*(c*s-(2/5)*s^2-c) := by
  have old := C1092MMMPOuterArmScalars.first cn sp hh hb hn order
  have correction := mul_nonneg
    (mul_nonneg (by norm_num : (0:ℝ)≤7/20) (sub_nonneg.mpr cn.2.1)) order
  have identity :
      (1/2+h^2/2+h*b/2+h*(c^2-(2/5)*c*s+s-2)+b*(c*s-(2/5)*s^2-c)) =
      (1/2+h^2/2+h*b/2+h*(c^2-(3/4)*c*s+s+(7/20)*s^2-2)+
        b*((13/20)*c*s-(2/5)*s^2-c+(7/20)*c^2))+
        (7/20)*(c-s)*(s*h-c*b) := by ring
  rw [identity]
  exact add_nonneg old correction

theorem second {c s h b : ℝ} (cn : Normal c s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : s*h-c*b≤0) :
    0≤1/2+h^2/2+h*b/2+h*(1-(37/50)*s^2-(2/5)*c*s-2)+
      b*((37/50)*c*s-(2/5)*s^2) := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have products := mul_nonneg (show 0≤c*b-s*h by linarith only [order])
    (add_nonneg (mul_nonneg cp hb) (mul_nonneg cn.1 hh))
  have relation : (c*b)^2-(s*h)^2=b^2-s^2 := by
    linear_combination b^2*cn.2.2-s^2*hn
  have blarge : s≤b := by nlinarith only [products,relation,cn.1,hb]
  have difference := mul_nonneg (sub_nonneg.mpr blarge) (add_nonneg cn.1 hb)
  have hsmall : h≤c := by nlinarith only [hn,cn.2.2,difference,hh,cp]
  have quadratic := C1092MMMPOuterArmScalars.quadratic_monotone cn hh hb hn hsmall blarge
  let A := 1-(37/50)*s^2-(2/5)*c*s
  let B := (37/50)*c*s-(2/5)*s^2
  have an : A-1≤0 := by
    have product := mul_nonneg cp cn.1
    dsimp only [A]
    nlinarith only [sq_nonneg s,product]
  have bp : 0≤B := by
    have product := mul_nonneg cn.1
      (show 0≤(37/50)*c-(2/5)*s by linarith only [cp,cn.2.1])
    dsimp only [B]
    nlinarith only [product]
  have firstProduct := mul_nonneg (sub_nonneg.mpr hsmall) (neg_nonneg.mpr an)
  have lastProduct := mul_nonneg (sub_nonneg.mpr blarge) bp
  have equality : (1-c)^2/2+c*s/2+c*(A-1)+s*B=((1-c)^2+s*(c-4/5))/2 := by
    dsimp only [A,B]
    linear_combination (-(2/5)*s)*cn.2.2
  have decomposition : 1/2+h^2/2+h*b/2+h*(A-2)+b*B =
      (((1-c)^2+s*(c-4/5))/2)+
        ((1-h)^2+h*b-(1-c)^2-c*s)/2+(c-h)*(-(A-1))+(b-s)*B := by
    rw [←equality]
    ring
  change 0≤1/2+h^2/2+h*b/2+h*(A-2)+b*B
  rw [decomposition]
  exact add_nonneg
    (add_nonneg (add_nonneg (C1092MMMPOuterArmScalars.endpoint cn)
      (div_nonneg (sub_nonneg.mpr quadratic) (by norm_num))) firstProduct) lastProduct

#print axioms first
#print axioms second
end N12Compact.Completion.OtherCases.C1089.ContinuousAnchorScalars
