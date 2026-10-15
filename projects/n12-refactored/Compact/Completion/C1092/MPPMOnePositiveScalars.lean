import Compact.Completion.C1092.MPPMMissingNegativeCrosspointG11

/-! ONE-POSITIVE-CONTINUOUS-ENDING Lemma 2, longitudinal scalar.
The full successor interval is treated by quadratic circle interpolation.
A sum-coordinate completed square proves its complete remainder, replacing
the manuscript's second-derivative estimate. Both endpoints have the same
rational1/100 reserve. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMOnePositive
open C977CornerCubic C1092ShallowPositiveScalars
open C1092MPPMCrosspointSupport C1092MPPMCrosspointSupport.QuadraticArc
set_option Elab.async false
noncomputable section

def positiveP (d t : ℝ) : ℝ := 2-d-t+(11/25)*d*t
def positiveQ (d t : ℝ) : ℝ := 1-d+t-(11/25)*t^2

private theorem positive_remainder (c s q z r : ℝ) (cn : Normal c s) (close : 97/100≤c)
    (qn : 0≤q) (qu : q≤5/12) (zn : 0≤z) (zu : z≤5/12)
    (rn : 0≤r) (ru : r≤5/12) :
    0≤remainder (-(11/25)*s) (-(11/25)*c) (99/100-2*c-(14/25)*s) q z r := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have Sn : 0≤sum3 q z r := by dsimp [sum3]; positivity
  have Pn : 0≤pair3 q z r := by dsimp [pair3]; positivity
  have Rn : 0≤triple3 q z r := by dsimp [triple3]; positivity
  have zr := mul_le_mul zu ru rn (by norm_num : (0:ℝ)≤5/12)
  have bound := mul_nonneg qn (show 0≤1-z*r by nlinarith only [zr])
  have RS : triple3 q z r≤sum3 q z r := by
    dsimp [triple3,sum3]
    nlinarith only [bound,zn,rn]
  have square := mul_nonneg (sub_nonneg.mpr RS) (add_nonneg Sn Rn)
  have Xcap : X q z r≤1 := by dsimp [X]; nlinarith only [square,sq_nonneg (pair3 q z r)]
  have RP := mul_nonneg Rn Pn
  have Ycap : Y q z r≤sum3 q z r := by dsimp [Y]; linarith only [RP]
  have Zidentity : 3*(Z q z r-1)-(sum3 q z r)^2=
      (q-z)^2+(q-r)^2+(z-r)^2+
        3*((q*z)^2+(q*r)^2+(z*r)^2+(q*z*r)^2) := by
    dsimp [Z,sum3]
    ring
  have Zlow : 1+(sum3 q z r)^2/3≤Z q z r := by
    nlinarith only [Zidentity,sq_nonneg (q-z),sq_nonneg (q-r),sq_nonneg (z-r),
      sq_nonneg (q*z),sq_nonneg (q*r),sq_nonneg (z*r),sq_nonneg (q*z*r)]
  have Zbase : 1≤Z q z r := by nlinarith only [Zlow,sq_nonneg (sum3 q z r)]
  have first := mul_nonneg (show 0≤2*c-99/100 by linarith only [close])
    (show 0≤Z q z r-1-(sum3 q z r)^2/3 by linarith only [Zlow])
  have second := mul_nonneg (show 0≤2*c-99/100-47/50 by linarith only [close])
    (show 0≤1+(sum3 q z r)^2/3 by positivity)
  have third := mul_nonneg cp (show 0≤sum3 q z r-Y q z r by linarith only [Ycap])
  have fourth := mul_nonneg (show 0≤1-c by linarith only [cb.2.1]) Sn
  have fifth := mul_nonneg cn.1 (show 0≤Z q z r-1 by linarith only [Zbase])
  have sixth := mul_nonneg cn.1 (show 0≤1-X q z r by linarith only [Xcap])
  have margin := sq_nonneg (sum3 q z r-66/47)
  dsimp [remainder]
  nlinarith only [first,second,third,fourth,fifth,sixth,margin,cn.1]

/-- The complete longitudinal gap against a positive missing recipient.
Its own half-angle lower bound is retained as an input of this scalar
theorem; the later actual-square adapter must produce that bound. -/
theorem positive_longitudinal (c s d t : ℝ) (cn : Normal c s)
    (close : 97/100≤c) (small : 4*s≤c) (en : Normal d t)
    (large : 13/87≤half d t) :
    1/100≤1-positiveP d t*c-positiveQ d t*s := by
  have cb := normal_bounds cn
  have cp : 0≤c := by linarith only [cb.1]
  have hd := normal_half en
  have rb := rho_bounds
  have norm0 := C1092MPPMNonpositivePredecessor.norm_le
    (9/10) (2/5) c s (99/100) cn.2.2 (by norm_num) (by norm_num)
  have norm1 := C1092MPPMNonpositivePredecessor.norm_le
    (91/100) (19/50) c s (99/100) cn.2.2 (by norm_num) (by norm_num)
  have normLast : (81/100)*c+(39/50)*s≤99/100 := by linarith only [norm1,small]
  have rem := positive_remainder c s (13/87) (half d t) rho cn close
    (by norm_num) (by norm_num) hd.1 (le_trans hd.2.1 rb.2.1.le) rb.1.le rb.2.1.le
  have first : 0≤value (-(11/25)*s) (-(11/25)*c) (99/100-2*c-(14/25)*s)
      (c+s) (c-s) (13/87) := by
    norm_num [value,cosH,sinH]
    nlinarith only [norm0,cp,cn.1]
  let v := Real.sqrt 2/2
  have vp : 0≤v := by dsimp [v]; positivity
  have vn : Normal v v := by
    refine ⟨vp,le_rfl,?_⟩
    dsimp [v]
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  have vlow : 707/1000≤v := by
    apply le_of_not_gt
    intro bad
    have square := mul_pos (show 0<707/1000-v by linarith only [bad])
      (show 0<707/1000+v by linarith only [vp])
    nlinarith only [square,vn.2.2]
  have endpointIdentity : value (-(11/25)*s) (-(11/25)*c) (99/100-2*c-(14/25)*s)
      (c+s) (c-s) rho=99/100-(111/50)*c-(39/50)*s+2*c*v := by
    dsimp [value]
    rw [rb.2.2.2.1,rb.2.2.2.2]
    change -(11/25)*s*v^2-(11/25)*c*v*v+(99/100-2*c-(14/25)*s)+
      (c+s)*v+(c-s)*v=99/100-(111/50)*c-(39/50)*s+2*c*v
    linear_combination (-(11/50)*(c+s))*vn.2.2
  have last : 0≤value (-(11/25)*s) (-(11/25)*c) (99/100-2*c-(14/25)*s)
      (c+s) (c-s) rho := by
    rw [endpointIdentity]
    have product := mul_nonneg cp (show 0≤v-707/1000 by linarith only [vlow])
    nlinarith only [normLast,product,cp]
  have result := nonnegative (-(11/25)*s) (-(11/25)*c) (99/100-2*c-(14/25)*s)
    (c+s) (c-s) (13/87) (half d t) rho (by norm_num) large hd.2.1 rem first last
  dsimp [value] at result
  rw [hd.2.2.2.1,hd.2.2.2.2] at result
  have identity : -(11/25)*s*d^2-(11/25)*c*d*t+(99/100-2*c-(14/25)*s)+
      (c+s)*d+(c-s)*t=
        1-positiveP d t*c-positiveQ d t*s-1/100 := by
    dsimp [positiveP,positiveQ]
    linear_combination (-(11/25)*s)*en.2.2
  rw [identity] at result
  linarith only [result]

/-- The alternating missing-negative successor has a different Q
coefficient. A cone-adjusted Cauchy bound proves its own gap directly. -/
theorem missing_negative_longitudinal (c s d t : ℝ) (cn : Normal c s)
    (small : 4*s≤c) (en : Normal d t) (large : 252/373≤t) :
    1/200≤1-(2-d-t+(11/25)*d*t)*c-(1+d-t-(11/25)*d^2)*s := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cp : 0≤c := by linarith only [cb.1]
  have sum := C1092MPPMMissingNegativeCrosspointSupport.large_sum en large
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := C977CornerSectorBounds.cosine_order en endpoint large
  have dt : d*t≤1/2 := by nlinarith only [en.2.2,sq_nonneg (d-t)]
  have order := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤d+t by linarith only [eb.1,en.1])
  have dd : 1/2≤d^2 := by nlinarith only [order,en.2.2]
  have Pcap : 2-d-t+(11/25)*d*t≤81/100 := by linarith only [sum,dt]
  have Qcap : 1+d-t-(11/25)*d^2≤17/20 := by linarith only [cosine,large,dd]
  have norm := C1092MPPMNonpositivePredecessor.norm_le
    (24/25) (1/4) c s (199/200) cn.2.2 (by norm_num) (by norm_num)
  have cone : (81/100)*c+(17/20)*s≤199/200 := by linarith only [norm,small]
  have first := mul_le_mul_of_nonneg_right Pcap cp
  have last := mul_le_mul_of_nonneg_right Qcap cn.1
  linarith only [first,last,cone]

end
#print axioms positive_longitudinal
#print axioms missing_negative_longitudinal
end N12Compact.C1092MPPMOnePositive
