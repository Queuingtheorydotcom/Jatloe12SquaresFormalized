import Compact.Completion.C1092.MPPMElbowIsolationScalars

/-! Full-interval successor margins. Unit-frame identities replace the
displayed quartic in ELBOW-SUCCESSOR §2.2: kappa≥7/10,
sigma≤t and t²≤2(1-d) suffice. The last transverse margin is the exact
endpoint projection identity, with its nonnegative tangent correction. -/
namespace N12Compact.C1092MPPMElbowSuccessorScalars
open C977CornerCubic C1092MPPMElbowScalars
set_option Elab.async false
noncomputable section

theorem own_before {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (order : sigma c s d t≤0) :
    0≤1+kappa c s d t-c-(2/5)*s-kappa c s d t*d+
      (2/5)*kappa c s d t*t-sigma c s d t*(d+(2/5)*t) := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  rcases frames cn dn with ⟨kp,_,_,_,sform,_,_,_⟩
  have first := mul_nonneg (show 0≤kappa c s d t by linarith only [kp])
    (sub_nonneg.mpr db.2.1)
  have last := mul_nonneg (neg_nonneg.mpr order)
    (show 0≤(3/5)*d+(2/5)*t by linarith only [db.1,dn.1])
  nlinarith only [cb.2.1,first,last,sform]

theorem own_after {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (order : 0≤sigma c s d t) :
    0≤1-c-(2/5)*s+kappa c s d t*(1-d+(2/5)*t)-
      (7/20)*sigma c s d t*(d+t) := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  rcases frames cn dn with ⟨kp,_,_,_,sform,_,_,cap⟩
  have first := mul_le_mul_of_nonneg_right kp.le (sub_nonneg.mpr db.2.1)
  have deficit : t^2≤2*(1-d) := by nlinarith only [dn.2.2,sq_nonneg (1-d)]
  have last := mul_nonneg (sub_nonneg.mpr cap) dn.1
  have rest := mul_nonneg order (show 0≤d by linarith only [db.1])
  nlinarith only [cb.2.1,first,deficit,last,rest,sform]

theorem transverse_before {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (sum : c+s<31/25) (order : sigma c s d t≤0) :
    0<kappa c s d t*(1-(7/10)*(c+s))-
      sigma c s d t*(1+(7/20)*c-(9/100)*s) := by
  have cb := normal_bounds cn
  have kp := (frames cn dn).1
  have first := mul_pos (show 0<kappa c s d t by linarith only [kp])
    (show 0<1-(7/10)*(c+s) by linarith only [sum])
  have last := mul_nonneg (neg_nonneg.mpr order)
    (show 0≤1+(7/20)*c-(9/100)*s by linarith only [cb.1,cn.2.1])
  nlinarith only [first,last]

theorem transverse_after_small {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (small : s<7/25) (sum : c+s<31/25) (order : 0≤sigma c s d t)
    (dc : 47/50<d) (ts : t<8/25) :
    0<kappa c s d t*(1-(7/10)*(c+s))+
      sigma c s d t*(1-(27/20)*c-(1/20)*s) := by
  have cb := normal_bounds cn
  rcases frames cn dn with ⟨kp,_,_,_,_,_,dform,cap⟩
  have first := mul_nonneg (show 0≤kappa c s d t by linarith only [kp])
    (sub_nonneg.mpr cb.2.1)
  have last := mul_nonneg order cn.1
  have kd : d≤kappa c s d t := by nlinarith only [first,last,dform]
  have kHigh : 47/50<kappa c s d t := lt_of_lt_of_le dc kd
  have lSmall : sigma c s d t<8/25 := lt_of_le_of_lt cap ts
  have weighted1 := mul_le_mul_of_nonneg_left
    (show 33/250≤1-(7/10)*(c+s) by linarith only [sum])
    (show 0≤kappa c s d t by linarith only [kp])
  have weighted2 := mul_le_mul_of_nonneg_left
    (show -(91/250)≤1-(27/20)*c-(1/20)*s by linarith only [cb.2.1,small]) order
  nlinarith only [weighted1,weighted2,kHigh,lSmall]

theorem transverse_corner {c s d t : ℝ} (cn : Normal c s) (dn : Normal d t)
    (close : 24/25<c) (small : s<7/25) :
    0<1+kappa c s d t+sigma c s d t-
      (27/20)*kappa c s d t*(c+s)-sigma c s d t*(2*c-(3/5)*s) := by
  have cb := normal_bounds cn
  have db := normal_bounds dn
  let A := (27/20)*(c+s)-1
  let B := 2*c-(3/5)*s-1
  let T := A*(c+s)+B*(c-s)
  let D := B*(c+s)-A*(c-s)
  have an : 0≤A := by dsimp [A]; linarith only [cb.2.2.2.2.1]
  have bn : 0≤B := by dsimp [B]; linarith only [close,small]
  have Tn : 0≤T := add_nonneg
    (mul_nonneg an (by linarith only [cb.2.2.2.2.1]))
    (mul_nonneg bn (sub_nonneg.mpr cn.2.1))
  have cross := mul_nonneg (show 0≤c by linarith only [cb.1]) cn.1
  have Did : D=13/20+(1/10)*s^2+(7/5)*c*s-2*s := by
    dsimp [D,A,B]
    linear_combination (13/20)*cn.2.2
  have Dn : 0≤D := by rw [Did]; nlinarith only [small,sq_nonneg s,cross]
  have Tid : T-27/20=(1-c)*(3/5-(7/5)*c)+(1/10)*c*s := by
    dsimp [T,A,B]
    linear_combination (39/20)*cn.2.2
  have correction := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr cb.2.1)
    (show 3/5-(7/5)*c≤0 by linarith only [close])
  have crossCap := mul_nonneg (sub_nonneg.mpr cb.2.1) cn.1
  have Tu : T<7/5 := by nlinarith only [Tid,correction,crossCap,small]
  have radial := mul_le_mul_of_nonneg_left db.2.2.2.2.2 Tn
  have tangent := mul_nonneg Dn (sub_nonneg.mpr dn.2.1)
  have identity : 2*(A*kappa c s d t+B*sigma c s d t)=T*(d+t)-D*(d-t) := by
    dsimp [T,D,A,B,kappa,sigma]
    ring
  have cap : A*kappa c s d t+B*sigma c s d t<1 := by
    nlinarith only [identity,radial,tangent,Tu]
  dsimp [A,B] at cap
  nlinarith only [cap]

theorem corner_angle {d t : ℝ} (dn : Normal d t)
    (cut : 130*t<43*d) : 47/50<d ∧ t<8/25 := by
  have db := normal_bounds dn
  have squared := mul_pos (show 0<43*d-130*t by linarith only [cut])
    (show 0<43*d+130*t by linarith only [db.1,dn.1])
  constructor
  · apply lt_of_not_ge
    intro bad
    have gap := mul_nonneg (show 0≤47/50-d by linarith only [bad])
      (show 0≤47/50+d by linarith only [db.1])
    nlinarith only [squared,gap,dn.2.2]
  · apply lt_of_not_ge
    intro bad
    have gap := mul_nonneg (show 0≤t-8/25 by linarith only [bad])
      (show 0≤t+8/25 by linarith only [dn.1])
    nlinarith only [squared,gap,dn.2.2]

theorem narrow_width {d t : ℝ} (dn : Normal d t) (width : 1<d+(43/500)*t) :
    130*t<43*d := by
  have db := normal_bounds dn
  have squared := mul_pos (sub_pos.mpr width)
    (show 0<d+(43/500)*t+1 by linarith only [db.1,dn.1])
  apply lt_of_not_ge
  intro bad
  have product := mul_nonneg dn.1 (show 0≤130*t-43*d by linarith only [bad])
  nlinarith only [squared,product,dn.2.2,sq_nonneg t]

#print axioms own_after
#print axioms transverse_corner
end
end N12Compact.C1092MPPMElbowSuccessorScalars
