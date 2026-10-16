import Compact.Completion.C1092.ShortWallPenalty

/-! The remaining small central-angle part of the MMMP center-to-crosspoint
argument. The strict shared wall segment has already reduced s to s<.22;
the slightly larger bound s≤1/4 below permits elementary algebra on both
complete relative-angle intervals. No orientation sampling is used. -/
namespace N12Compact.C1092MMMPCenterCrosspointScalars
open C977CornerCubic
set_option Elab.async false

private theorem small_bounds {c s : ℝ} (cn : Normal c s) (small : s≤1/4) :
    19/20≤c ∧ 1-c≤(13/25)*s^2 := by
  have cb := normal_bounds cn
  have cnon : 0≤c := by linarith only [cb.1]
  have sprod := mul_nonneg (show 0≤1/4-s by linarith only [small])
    (show 0≤1/4+s by linarith only [cn.1])
  have clower : 19/20≤c := by
    nlinarith only [cn.2.2,sprod,cnon]
  have product := mul_nonneg (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤(13/25)*(1+c)-1 by linarith only [clower])
  refine ⟨clower,?_⟩
  nlinarith only [product,cn.2.2]

private theorem order_bounds {c s h b : ℝ} (cn : Normal c s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) :
    c≤h ∧ b≤s := by
  have cb := normal_bounds cn
  have product := mul_nonneg order
    (add_nonneg (mul_nonneg cn.1 hh) (mul_nonneg (by linarith only [cb.1]) hb))
  have identity : (s*h)^2-(c*b)^2=s^2-b^2 := by
    linear_combination s^2*hn-b^2*cn.2.2
  have bsmall : b≤s := by nlinarith only [product,identity,cn.1,hb]
  have prod := mul_nonneg (sub_nonneg.mpr bsmall) (add_nonneg cn.1 hb)
  exact ⟨by nlinarith only [hn,cn.2.2,prod,hh,cb.1],bsmall⟩

/-- The exact F1 gap on the whole relative-angle interval 0≤phi≤p.
The side-length strictness in the geometric support bounds only requires
this weak gap, including the axial central endpoint. -/
theorem first {c s h b : ℝ} (cn : Normal c s) (small : s≤1/4)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) :
    0≤1/2+h^2/2+h*b/2+
      h*(c+s-(17/20)*c*s+(7/20)*s^2-2)+
      b*(s-c+(7/20)*c^2-(7/20)*c*s-s^2/2) := by
  have cb := normal_bounds cn
  obtain ⟨clower,defect⟩ := small_bounds cn small
  obtain ⟨hlarge,bsmall⟩ := order_bounds cn hh hb hn order
  have hone : h≤1 := by nlinarith only [hn,hh,sq_nonneg b]
  let A := c+s-(17/20)*c*s+(7/20)*s^2-1
  let B := s-c+(7/20)*c^2-(7/20)*c*s-s^2/2
  let D := B+h/2
  have Apos : 0≤A := by
    have first := mul_nonneg cn.1
      (show 0≤(3/20)-(17/100)*s by linarith only [small])
    have last := mul_nonneg cn.1
      (show 0≤1-c by linarith only [cb.2.1])
    dsimp [A]
    nlinarith only [first,last,defect]
  have Dneg : D≤0 := by
    have first := mul_nonneg cn.1
      (show 0≤c-19/20 by linarith only [clower])
    have last := mul_nonneg (show 0≤1/4-s by linarith only [small])
      (show 0≤267/400-(33/100)*(1/4+s) by linarith only [small])
    dsimp [D,B]
    nlinarith only [first,last,defect,hone,cn.2.2]
  have p1 := mul_nonneg (sub_nonneg.mpr hlarge) Apos
  have p2 := mul_nonneg (sub_nonneg.mpr bsmall) (neg_nonneg.mpr Dneg)
  have p3 := mul_nonneg cn.1 (sub_nonneg.mpr hlarge)
  have endpoint : c*A+s*(B+c/2)=(1-c)*(1-s/2) := by
    dsimp [A,B]
    linear_combination (1-s/2)*cn.2.2
  have endpos := mul_nonneg
    (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤1-s/2 by linarith only [small])
  have target : 0≤(1-h)^2/2+h*A+b*D := by
    have decomposition : (1-h)^2/2+h*A+b*D=
        (1-h)^2/2+(h-c)*A+(s-b)*(-D)+s*(h-c)/2+(1-c)*(1-s/2) := by
      rw [←endpoint]
      dsimp [D]
      ring
    rw [decomposition]
    exact add_nonneg
      (add_nonneg (add_nonneg (add_nonneg
        (div_nonneg (sq_nonneg (1-h)) (by norm_num)) p1) p2)
        (div_nonneg p3 (by norm_num))) endpos
  dsimp [A,D,B] at target
  nlinarith only [target]

theorem quadratic_monotone {c s h b : ℝ} (cn : Normal c s)
    (small : s≤1/4) (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1)
    (hsmall : h≤c) (blarge : s≤b) :
    (1-c)^2+c*s≤(1-h)^2+h*b := by
  have cb := normal_bounds cn
  have clower := (small_bounds cn small).1
  have bone : b≤1 := by nlinarith only [hn,hb,sq_nonneg h]
  have bracket : 0≤(b+s)*(2-c-h-s)+h*(c+h) := by
    by_cases hhalf : h≤1/2
    · have first := mul_nonneg (add_nonneg hb cn.1)
        (show 0≤2-c-h-s by linarith only [cb.2.1,hhalf,small])
      have last := mul_nonneg hh (show 0≤c+h by linarith only [clower,hh])
      nlinarith only [first,last]
    · have hhalf : 1/2≤h := by exact (lt_of_not_ge hhalf).le
      have first := mul_nonneg (add_nonneg hb cn.1)
        (show 0≤2-c-h by linarith only [cb.2.1,hsmall])
      have last := mul_nonneg (show 0≤h-1/2 by linarith only [hhalf])
        (show 0≤c+h by linarith only [clower,hhalf])
      have tail := mul_nonneg (show 0≤1/4-s by linarith only [small])
        (show 0≤b+s by linarith only [hb,cn.1])
      nlinarith only [first,last,tail,bone,small,clower,hhalf]
  have weighted := mul_nonneg (sub_nonneg.mpr hsmall) bracket
  have identity : (b+s)*((1-h)^2+h*b-(1-c)^2-c*s)=
      (c-h)*((b+s)*(2-c-h-s)+h*(c+h)) := by
    linear_combination h*hn-h*cn.2.2
  by_cases bs : b+s=0
  · have bz : b=0 := by linarith only [bs,hb,cn.1]
    have sz : s=0 := by linarith only [bs,hb,cn.1]
    have ho : h=1 := by nlinarith only [hn,bz,hh]
    have co : c=1 := by nlinarith only [cn.2.2,sz,clower]
    simp only [ho,co,bz,sz,sub_self,sq,zero_mul,mul_zero,add_zero,le_refl]
  · have bp : 0<b+s := lt_of_le_of_ne (add_nonneg hb cn.1) (Ne.symm bs)
    have scaled : 0≤(b+s)*((1-h)^2+h*b-(1-c)^2-c*s) := by
      linarith only [identity,weighted]
    have result := nonneg_of_mul_nonneg_right scaled bp
    linarith only [result]

/-- The exact F2 gap on the remaining full relative-angle interval p≤phi≤pi/2.
A monotone quadratic gap replaces the trigonometric derivative estimate. -/
theorem second {c s h b : ℝ} (cn : Normal c s) (small : s≤1/4)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : s*h-c*b≤0) :
    0≤1/2+h^2/2+h*b/2+
      h*(c-c*s/2-2)+b*(s-s^2/2) := by
  have cb := normal_bounds cn
  have cnon : 0≤c := by linarith only [cb.1]
  have product := mul_nonneg (show 0≤c*b-s*h by linarith only [order])
    (add_nonneg (mul_nonneg cnon hb) (mul_nonneg cn.1 hh))
  have identity : (c*b)^2-(s*h)^2=b^2-s^2 := by
    linear_combination b^2*cn.2.2-s^2*hn
  have blarge : s≤b := by nlinarith only [product,identity,cn.1,hb]
  have prod := mul_nonneg (sub_nonneg.mpr blarge) (add_nonneg cn.1 hb)
  have hsmall : h≤c := by nlinarith only [hn,cn.2.2,prod,hh,cnon]
  have quadratic := quadratic_monotone cn small hh hb hn hsmall blarge
  have Ap : c-c*s/2-1≤0 := by
    have prod := mul_nonneg cnon cn.1
    linarith only [prod,cb.2.1]
  have Bp : 0≤s-s^2/2 := by
    have prod := mul_nonneg cn.1 (show 0≤1-s/2 by linarith only [small])
    nlinarith only [prod]
  have p1 := mul_nonneg (sub_nonneg.mpr hsmall) (neg_nonneg.mpr Ap)
  have p2 := mul_nonneg (sub_nonneg.mpr blarge) Bp
  have endpoint : (1-c)^2/2+c*s/2+c*(c-c*s/2-1)+s*(s-s^2/2)=
      (1-c)*(3-c-s)/2 := by
    linear_combination (1-s/2)*cn.2.2
  have endpos := mul_nonneg
    (show 0≤1-c by linarith only [cb.2.1])
    (show 0≤3-c-s by linarith only [cb.2.1,small])
  nlinarith only [quadratic,p1,p2,endpoint,endpos]

#print axioms first
#print axioms second
end N12Compact.C1092MMMPCenterCrosspointScalars
