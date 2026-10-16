import Compact.Completion.C1092.MMMP.CenterCrosspointScalars

/-! Small-angle half-angle crossing gaps. In the physical application,
the actual compulsory wall point at height .39 forces this whole interval
before either complete-square support comparison is made. -/
namespace N12Compact.C1092MMMPNearCrossingScalars
open C977CornerCubic
set_option Elab.async false

theorem endpoint {c s z : ℝ} (cn : Normal c s) (zn : 0≤z) (zu : z≤1/2)
    (angle : z*(1+c)=s) (unitAngle : s*z=1-c) :
    0≤1-c-z+c*s/2 ∧ 0≤3/2-z-2*c+c^2/2+c*s/2 := by
  have cform : (1+z^2)*c=1-z^2 := by
    have times := congrArg (fun a : ℝ => a*z) angle
    nlinarith only [times,unitAngle]
  have sform : (1+z^2)*s=2*z := by
    have times := congrArg (fun a : ℝ => a*z) unitAngle
    nlinarith only [times,angle]
  have identity : (1+z^2)^2*(1-c-z+c*s/2)=z^2*(1-z)*(2-z+z^2) := by
    calc
      _ = (1+z^2)^2*(1-z)-(1+z^2)*((1+z^2)*c)+
          ((1+z^2)*c)*((1+z^2)*s)/2 := by ring
      _ = _ := by rw [cform,sform]; ring
  have product := mul_nonneg
    (mul_nonneg (sq_nonneg z) (show 0≤1-z by linarith only [zu]))
    (show 0≤2-z+z^2 by nlinarith only [zu,sq_nonneg z])
  have scaled : 0≤(1+z^2)^2*(1-c-z+c*s/2) := by rw [identity]; exact product
  have first := nonneg_of_mul_nonneg_right scaled
    (sq_pos_of_pos (show 0<1+z^2 by positivity))
  exact ⟨first,by nlinarith only [first,sq_nonneg (1-c)]⟩

theorem first {c s z h b : ℝ} (cn : Normal c s) (small : s≤1/4)
    (zn : 0≤z) (zu : z≤1/2) (angle : z*(1+c)=s) (unitAngle : s*z=1-c)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) :
    0≤1/2+h^2/2+h*b/2+h*(c+z-2)+b*(s-1) := by
  have cb := normal_bounds cn
  have products := mul_nonneg order
    (add_nonneg (mul_nonneg cn.1 hh) (mul_nonneg (by linarith only [cb.1]) hb))
  have relation : (s*h)^2-(c*b)^2=s^2-b^2 := by
    linear_combination s^2*hn-b^2*cn.2.2
  have bsmall : b≤s := by nlinarith only [products,relation,cn.1,hb]
  have difference := mul_nonneg (sub_nonneg.mpr bsmall) (add_nonneg cn.1 hb)
  have hlarge : c≤h := by nlinarith only [hn,cn.2.2,difference,hh,cb.1]
  have hone : h≤1 := by nlinarith only [hn,hh,sq_nonneg b]
  let A := c+z-1
  let B := s-1
  let D := B+h/2
  have apos : 0≤A := by
    have product := mul_nonneg zn (show 0≤1-s by linarith only [small])
    dsimp [A]
    nlinarith only [product,unitAngle]
  have dneg : D≤0 := by dsimp [D,B]; linarith only [small,hone]
  have p1 := mul_nonneg (sub_nonneg.mpr hlarge) apos
  have p2 := mul_nonneg (sub_nonneg.mpr bsmall) (neg_nonneg.mpr dneg)
  have p3 := mul_nonneg cn.1 (sub_nonneg.mpr hlarge)
  have endpos := (endpoint cn zn zu angle unitAngle).1
  have equality : c*A+s*(B+c/2)=1-c-z+c*s/2 := by
    dsimp [A,B]
    linear_combination cn.2.2+angle
  have decomposition : 1/2+h^2/2+h*b/2+h*(c+z-2)+b*(s-1)=
      (1-h)^2/2+(h-c)*A+(s-b)*(-D)+s*(h-c)/2+(1-c-z+c*s/2) := by
    rw [←equality]
    dsimp [A,B,D]
    ring
  rw [decomposition]
  exact add_nonneg
    (add_nonneg (add_nonneg (add_nonneg
      (div_nonneg (sq_nonneg (1-h)) (by norm_num)) p1) p2)
      (div_nonneg p3 (by norm_num))) endpos

theorem second {c s z h b : ℝ} (cn : Normal c s) (small : s≤1/4)
    (zn : 0≤z) (zu : z≤1/2) (angle : z*(1+c)=s) (unitAngle : s*z=1-c)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : s*h-c*b≤0) :
    0≤1/2+h^2/2+h*b/2+h*((1-z)*c+(13/50)*s^2-2)+
      b*((1-z)*s-(13/50)*s*c) := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have products := mul_nonneg (show 0≤c*b-s*h by linarith only [order])
    (add_nonneg (mul_nonneg cp hb) (mul_nonneg cn.1 hh))
  have relation : (c*b)^2-(s*h)^2=b^2-s^2 := by
    linear_combination b^2*cn.2.2-s^2*hn
  have blarge : s≤b := by nlinarith only [products,relation,cn.1,hb]
  have difference := mul_nonneg (sub_nonneg.mpr blarge) (add_nonneg cn.1 hb)
  have hsmall : h≤c := by nlinarith only [hn,cn.2.2,difference,hh,cp]
  have quadratic := C1092MMMPCenterCrosspointScalars.quadratic_monotone cn small hh hb hn hsmall blarge
  let A := (1-z)*c+(13/50)*s^2
  let B := (1-z)*s-(13/50)*s*c
  have zlower : s/2≤z := by
    have weight := mul_nonneg zn (show 0≤1-c by linarith only [cb.2.1])
    nlinarith only [weight,angle]
  have an : A-1≤0 := by
    have first := mul_nonneg (sub_nonneg.mpr zlower) cp
    have last := mul_nonneg cn.1 (show 0≤c/2-(13/50)*s by linarith only [cn.2.1,cp])
    dsimp [A]
    nlinarith only [first,last,cb.2.1]
  have bp : 0≤B := by
    have product := mul_nonneg cn.1 (show 0≤1-z-(13/50)*c by linarith only [zu,cb.2.1])
    dsimp [B]
    nlinarith only [product]
  have p1 := mul_nonneg (sub_nonneg.mpr hsmall) (neg_nonneg.mpr an)
  have p2 := mul_nonneg (sub_nonneg.mpr blarge) bp
  have endpos := (endpoint cn zn zu angle unitAngle).2
  have equality : (1-c)^2/2+c*s/2+c*(A-1)+s*B=3/2-z-2*c+c^2/2+c*s/2 := by
    dsimp [A,B]
    linear_combination (1-z)*cn.2.2
  have decomposition : 1/2+h^2/2+h*b/2+h*(A-2)+b*B=
      (3/2-z-2*c+c^2/2+c*s/2)+
        ((1-h)^2+h*b-(1-c)^2-c*s)/2+(c-h)*(-(A-1))+(b-s)*B := by
    rw [←equality]
    ring
  change 0≤1/2+h^2/2+h*b/2+h*(A-2)+b*B
  rw [decomposition]
  exact add_nonneg
    (add_nonneg (add_nonneg endpos (div_nonneg (by linarith only [quadratic]) (by norm_num))) p1) p2

#print axioms first
#print axioms second
end N12Compact.C1092MMMPNearCrossingScalars
