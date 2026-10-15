import Compact.Completion.C1092.ShortWallPenalty

/-! Exact whole-arc support gaps for the centered outer arm. A rational
half-angle identity supplies the quadratic chord correction, replacing
the analytic sine-interpolation argument of the reference. -/
namespace N12Compact.C1092MMMPOuterArmScalars
open C977CornerCubic
set_option Elab.async false

theorem endpoint {c s : ℝ} (cn : Normal c s) :
    0≤((1-c)^2+s*(c-4/5))/2 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  let z := s/(1+c)
  have den : 0<1+c := by linarith only [cp]
  have zn : 0≤z := div_nonneg cn.1 den.le
  have zu : z≤1/2 := by
    dsimp [z]
    apply (div_le_iff₀ den).mpr
    linarith only [cn.2.1,cb.2.2.2.1]
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [den.ne']
  have unitAngle : s*z=1-c := by
    dsimp [z]
    field_simp [den.ne']
    nlinarith only [cn.2.2]
  have cform : (1+z^2)*c=1-z^2 := by
    have times := congrArg (fun a : ℝ => a*z) angle
    dsimp at times
    nlinarith only [times,unitAngle]
  have sform : (1+z^2)*s=2*z := by
    have times := congrArg (fun a : ℝ => a*z) unitAngle
    dsimp at times
    nlinarith only [times,angle]
  have identity : (1+z^2)^2*(((1-c)^2+s*(c-4/5))/2)=
      z*(2*z-1)*(5*z^2-2*z-1)/5 := by
    calc
      _ = ((1+z^2)-(1+z^2)*c)^2/2+
          ((1+z^2)*s)*((1+z^2)*c-(4/5)*(1+z^2))/2 := by ring
      _ = _ := by rw [cform,sform]; ring
  have square := mul_nonneg zn (show 0≤1/2-z by linarith only [zu])
  have polynomial : 5*z^2-2*z-1≤0 := by nlinarith only [square,zu]
  have product := div_nonneg
    (mul_nonneg zn (mul_nonneg_of_nonpos_of_nonpos
      (show 2*z-1≤0 by linarith only [zu]) polynomial)) (by norm_num : (0:ℝ)≤5)
  have scaled : 0≤(1+z^2)^2*(((1-c)^2+s*(c-4/5))/2) := by
    rw [identity]
    exact product
  exact nonneg_of_mul_nonneg_right scaled (sq_pos_of_pos (by positivity))

/-- The quadratic part increases on the whole first-quadrant arc.
The central frame is canonical, but the other angle is unrestricted. -/
theorem quadratic_monotone {c s h b : ℝ} (cn : Normal c s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (hc : h≤c) (sb : s≤b) :
    (1-c)^2+c*s≤(1-h)^2+h*b := by
  have cb := normal_bounds cn
  have bone : b≤1 := by nlinarith only [hn,hb,sq_nonneg h]
  have bracket : 0≤(b+s)*(2-c-h-s)+h*(c+h) := by
    by_cases sign : 0≤2-c-h-s
    · exact add_nonneg (mul_nonneg (add_nonneg hb cn.1) sign)
        (mul_nonneg hh (by linarith only [cb.1,hh]))
    · have first := mul_nonpos_of_nonneg_of_nonpos
        (show 0≤2-b-s by linarith only [bone,cb.2.2.2.1])
        (show 2-c-h-s≤0 by exact (lt_of_not_ge sign).le)
      have last := mul_nonneg hh (show 0≤c-7/10 by linarith only [cb.1])
      have sum := normal_bounds cn
      nlinarith only [first,last,sum.2.2.2.2.2,sq_nonneg (h-13/20)]
  have weighted := mul_nonneg (sub_nonneg.mpr hc) bracket
  have identity : (b+s)*((1-h)^2+h*b-(1-c)^2-c*s)=
      (c-h)*((b+s)*(2-c-h-s)+h*(c+h)) := by
    linear_combination h*hn-h*cn.2.2
  by_cases zero : b+s=0
  · have bz : b=0 := by linarith only [zero,hb,cn.1]
    have sz : s=0 := by linarith only [zero,hb,cn.1]
    have ho : h=1 := by nlinarith only [hn,bz,hh]
    have co : c=1 := by nlinarith only [cn.2.2,sz,cb.1]
    simp only [ho,co,bz,sz,sub_self,sq,zero_mul,mul_zero,add_zero,le_refl]
  · have positive : 0<b+s := lt_of_le_of_ne (add_nonneg hb cn.1) (Ne.symm zero)
    have scaled : 0≤(b+s)*((1-h)^2+h*b-(1-c)^2-c*s) := by
      rw [identity]
      exact weighted
    have result := nonneg_of_mul_nonneg_right scaled positive
    linarith only [result]

private theorem order_bounds {c s h b : ℝ} (cn : Normal c s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) : c≤h ∧ b≤s := by
  have cb := normal_bounds cn
  have product := mul_nonneg order
    (add_nonneg (mul_nonneg cn.1 hh) (mul_nonneg (by linarith only [cb.1]) hb))
  have identity : (s*h)^2-(c*b)^2=s^2-b^2 := by
    linear_combination s^2*hn-b^2*cn.2.2
  have bsmall : b≤s := by nlinarith only [product,identity,cn.1,hb]
  have difference := mul_nonneg (sub_nonneg.mpr bsmall) (add_nonneg cn.1 hb)
  exact ⟨by nlinarith only [hn,cn.2.2,difference,hh,cb.1],bsmall⟩

private theorem arc_correction {c s h b : ℝ} (cn : Normal c s) (sp : 0<s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) :
    0≤s*((1-h)^2+h*b)-b*((1-c)^2+c*s) := by
  have cb := normal_bounds cn
  obtain ⟨hlarge,bsmall⟩ := order_bounds cn hh hb hn order
  let z := s/(1+c)
  let k := b/(1+h)
  have dc : 0<1+c := by linarith only [cb.1]
  have dh : 0<1+h := by linarith only [hh]
  have zn : 0≤z := div_nonneg cn.1 dc.le
  have kn : 0≤k := div_nonneg hb dh.le
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [dc.ne']
  have wallAngle : k*(1+h)=b := by dsimp [k]; field_simp [dh.ne']
  have unitAngle : s*z=1-c := by
    dsimp [z]
    field_simp [dc.ne']
    nlinarith only [cn.2.2]
  have wallUnit : b*k=1-h := by
    dsimp [k]
    field_simp [dh.ne']
    nlinarith only [hn]
  have zu : z≤1/2 := by
    dsimp [z]
    apply (div_le_iff₀ dc).mpr
    linarith only [cn.2.1,cb.2.2.2.1]
  have kz : k≤z := by
    dsimp [k]
    apply (div_le_iff₀ dh).mpr
    have product := mul_nonneg zn (sub_nonneg.mpr hlarge)
    nlinarith only [angle,bsmall,product]
  have cform : (1+z^2)*(1-c)=2*z^2 := by
    have times := congrArg (fun a : ℝ => a*z) angle
    dsimp at times
    nlinarith only [times,unitAngle]
  have hform : (1+k^2)*(1-h)=2*k^2 := by
    have times := congrArg (fun a : ℝ => a*k) wallAngle
    dsimp at times
    nlinarith only [times,wallUnit]
  have zk : 0≤z*k := mul_nonneg zn kn
  have zkSmall : z*k≤1 := by
    have product := mul_nonneg kn (show 0≤1/2-z by linarith only [zu])
    nlinarith only [product,kz,zu]
  have bracket := add_nonneg
    (mul_nonneg (add_nonneg zn kn) (show 0≤1-z-k by linarith only [zu,kz]))
    (mul_nonneg zk (sub_nonneg.mpr zkSmall))
  have factored := mul_nonneg
    (mul_nonneg (by norm_num : (0:ℝ)≤2) (sub_nonneg.mpr kz)) bracket
  have identity : (1+z^2)*(1+k^2)*((1-c)*(1-z)-(1-h)*(1-k))=
      2*(z-k)*((z+k)*(1-z-k)+z*k*(1-z*k)) := by
    calc
      _ = (1+k^2)*((1+z^2)*(1-c))*(1-z)-
          (1+z^2)*((1+k^2)*(1-h))*(1-k) := by ring
      _ = _ := by rw [cform,hform]; ring
  have scaled : 0≤(1+z^2)*(1+k^2)*((1-c)*(1-z)-(1-h)*(1-k)) := by
    rw [identity]
    exact factored
  have gap := nonneg_of_mul_nonneg_right scaled
    (mul_pos (by positivity : 0<1+z^2) (by positivity : 0<1+k^2))
  have result := mul_nonneg (mul_nonneg cn.1 hb) gap
  have correction : s*((1-h)^2+h*b)-b*((1-c)^2+c*s)=
      s*b*((1-c)*(1-z)-(1-h)*(1-k)) := by
    calc
      _ = s*b*(h-c)+s*(1-h)*(1-h)-b*(1-c)*(1-c) := by ring
      _ = s*b*(h-c)+s*(1-h)*(b*k)-b*(1-c)*(s*z) := by rw [wallUnit,unitAngle]
      _ = _ := by ring
  rwa [correction]

theorem first {c s h b : ℝ} (cn : Normal c s) (sp : 0<s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : 0≤s*h-c*b) :
    0≤1/2+h^2/2+h*b/2+
      h*(c^2-(3/4)*c*s+s+(7/20)*s^2-2)+
      b*((13/20)*c*s-(2/5)*s^2-c+(7/20)*c^2) := by
  let A := c^2-(3/4)*c*s+s+(7/20)*s^2
  let B := (13/20)*c*s-(2/5)*s^2-c+(7/20)*c^2
  let E := ((1-c)^2+s*(c-4/5))/2
  have short : (3/4)*c+(13/20)*s<1 := by
    nlinarith only [cn.2.2,sq_nonneg ((13/20)*c-(3/4)*s),
      sq_nonneg ((3/4)*c+(13/20)*s-1)]
  have e0 : 0≤A-1 := by
    have product := mul_nonneg cn.1 (show 0≤1-(3/4)*c-(13/20)*s by linarith only [short])
    dsimp [A]
    nlinarith only [cn.2.2,product]
  have endIdentity : 1/2+c^2/2+c*s/2+c*(A-2)+s*B=E := by
    dsimp [A,B,E]
    linear_combination (c-(2/5)*s)*cn.2.2
  have correction := arc_correction cn sp hh hb hn order
  have decomposition : s*(1/2+h^2/2+h*b/2+h*(A-2)+b*B)=
      (s*h-c*b)*(A-1)+b*E+
        (s*((1-h)^2+h*b)-b*((1-c)^2+c*s))/2 := by
    rw [←endIdentity]
    ring
  have scaled : 0≤s*(1/2+h^2/2+h*b/2+h*(A-2)+b*B) := by
    rw [decomposition]
    exact add_nonneg (add_nonneg (mul_nonneg order e0)
      (mul_nonneg hb (endpoint cn))) (div_nonneg correction (by norm_num))
  exact nonneg_of_mul_nonneg_right scaled sp

theorem second {c s h b : ℝ} (cn : Normal c s)
    (hh : 0≤h) (hb : 0≤b) (hn : h^2+b^2=1) (order : s*h-c*b≤0) :
    0≤1/2+h^2/2+h*b/2+h*(c^2-(2/5)*c*s-2)+b*(c*s-(2/5)*s^2) := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have products := mul_nonneg (show 0≤c*b-s*h by linarith only [order])
    (add_nonneg (mul_nonneg cp hb) (mul_nonneg cn.1 hh))
  have relation : (c*b)^2-(s*h)^2=b^2-s^2 := by
    linear_combination b^2*cn.2.2-s^2*hn
  have blarge : s≤b := by nlinarith only [products,relation,cn.1,hb]
  have difference := mul_nonneg (sub_nonneg.mpr blarge) (add_nonneg cn.1 hb)
  have hsmall : h≤c := by nlinarith only [hn,cn.2.2,difference,hh,cp]
  have quadratic := quadratic_monotone cn hh hb hn hsmall blarge
  let A := c^2-(2/5)*c*s
  let B := c*s-(2/5)*s^2
  have an : A-1≤0 := by
    have product := mul_nonneg cp cn.1
    dsimp [A]
    nlinarith only [cn.2.2,sq_nonneg s,product]
  have bp : 0≤B := by
    have product := mul_nonneg cn.1 (show 0≤c-(2/5)*s by linarith only [cn.1,cn.2.1])
    dsimp [B]
    nlinarith only [product]
  have firstProduct := mul_nonneg (sub_nonneg.mpr hsmall) (neg_nonneg.mpr an)
  have lastProduct := mul_nonneg (sub_nonneg.mpr blarge) bp
  have equality : (1-c)^2/2+c*s/2+c*(A-1)+s*B=((1-c)^2+s*(c-4/5))/2 := by
    dsimp [A,B]
    linear_combination (c-(2/5)*s)*cn.2.2
  have decomposition : 1/2+h^2/2+h*b/2+h*(A-2)+b*B=
      (((1-c)^2+s*(c-4/5))/2)+
        ((1-h)^2+h*b-(1-c)^2-c*s)/2+(c-h)*(-(A-1))+(b-s)*B := by
    rw [←equality]
    ring
  change 0≤1/2+h^2/2+h*b/2+h*(A-2)+b*B
  rw [decomposition]
  exact add_nonneg
    (add_nonneg (add_nonneg (endpoint cn) (div_nonneg (sub_nonneg.mpr quadratic) (by norm_num)))
      firstProduct) lastProduct

#print axioms first
#print axioms second
end N12Compact.C1092MMMPOuterArmScalars
