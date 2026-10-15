import Compact.Completion.C1092.MPPMNegativeCrosspointCentral

/-! NEGATIVE-WALL-SCALARS §5. Exact finite unit-circle differences
give both decreasing successor coefficients; all bounds retain t=0 and
the slope endpoint 8t=3d. No trigonometric derivatives are required. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

theorem second_order {d t d₀ t₀ : ℝ} (en : Normal d t) (base : Normal d₀ t₀)
    (shallow : 8*t≤3*d) (shallow₀ : 8*t₀≤3*d₀) (order : t₀≤t) :
    P2 d t≤P2 d₀ t₀ ∧ Q2 d t≤Q2 d₀ t₀ := by
  have eb := normal_bounds en
  have bb := normal_bounds base
  have es := shallow_bounds en shallow
  have bs := shallow_bounds base shallow₀
  let D := d+d₀
  let T := t+t₀
  let Jp := T*((61/100)*D-1)-(13/40)*(D^2-T^2)
  let Jq := -D+(13/20)*D*T+(61/200)*(D^2-T^2)
  have Dl : 93/50≤D := by dsimp [D]; linarith only [es.1,bs.1]
  have Du : D≤2 := by dsimp [D]; linarith only [eb.2.1,bb.2.1]
  have Tn : 0≤T := add_nonneg en.1 base.1
  have Tu : T≤18/25 := by dsimp [T]; linarith only [es.2,bs.2]
  have dsquare := mul_nonneg (show 0≤D-93/50 by linarith only [Dl])
    (show 0≤D+93/50 by linarith only [Dl])
  have tsquare := mul_nonneg (show 0≤18/25-T by linarith only [Tu])
    (show 0≤18/25+T by linarith only [Tn])
  have dt := mul_nonneg Tn (show 0≤2-D by linarith only [Du])
  have jp : Jp≤0 := by
    dsimp [Jp]
    nlinarith only [dsquare,tsquare,dt,Tu]
  have dstep := mul_nonneg (show 0≤2-D by linarith only [Du])
    (show 0≤-1+(13/20)*T+(61/200)*(2+D) by linarith only [Dl,Tn])
  have tstep := mul_nonneg (show 0≤18/25-T by linarith only [Tu])
    (show 0≤13/10-(61/200)*(18/25+T) by linarith only [Tu])
  have jq : Jq≤0 := by dsimp [Jq]; nlinarith only [dstep,tstep]
  have pi : D*(P2 d t-P2 d₀ t₀)=(t-t₀)*Jp := by
    dsimp [D,T,Jp,P2]
    linear_combination (-1+(13/40)*(t+t₀))*base.2.2-
      (-1+(13/40)*(t+t₀))*en.2.2
  have qi : D*(Q2 d t-Q2 d₀ t₀)=(t-t₀)*Jq := by
    dsimp [D,T,Jq,Q2]
    linear_combination (-(61/200)*(t+t₀))*base.2.2-
      (-(61/200)*(t+t₀))*en.2.2
  have first := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr order) jp
  have last := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr order) jq
  rw [←pi] at first
  rw [←qi] at last
  have dp : 0<D := by linarith only [Dl]
  have resultP := nonpos_of_mul_nonpos_right first dp
  have resultQ := nonpos_of_mul_nonpos_right last dp
  exact ⟨by linarith only [resultP],by linarith only [resultQ]⟩

theorem coefficient_bounds {d t : ℝ} (en : Normal d t) (shallow : 8*t≤3*d) :
    0≤P d t ∧ P d t≤3/10 ∧ 0≤1-Q d t ∧ 1-Q d t≤1/5 ∧
      1-Q d t≤P d t ∧ 1/3<P2 d t ∧ P2 d t≤13/20 ∧
      -1-t≤Q2 d t ∧ Q2 d t≤-1 ∧ 0<1-(61/100)*d-(13/20)*t := by
  have eb := normal_bounds en
  have small := shallow_bounds en shallow
  have dp : 0≤d := by linarith only [eb.1]
  have dt := mul_nonneg dp en.1
  have dtcap := mul_le_mul_of_nonneg_right eb.2.1 en.1
  have tsquare := mul_nonneg (show 0≤9/25-t by linarith only [small.2])
    (show 0≤9/25+t by linarith only [en.1])
  have first := mul_nonneg en.1
    (show 0≤(37/50)*d-(13/50)*t by linarith only [en.2.1,dp])
  have pn : 0≤P d t := by dsimp [P]; nlinarith only [first]
  have ph : P d t≤3/10 := by dsimp [P]; nlinarith only [dtcap,small.2,sq_nonneg t]
  have Sn : 0≤1-Q d t := by dsimp [Q]; nlinarith only [dt,sq_nonneg t]
  have Sh : 1-Q d t≤1/5 := by dsimp [Q]; nlinarith only [dtcap,small.2,tsquare]
  have gap := mul_nonneg en.1 (show 0≤(12/25)*d-t by linarith only [shallow,dp])
  have SP : 1-Q d t≤P d t := by dsimp [P,Q]; nlinarith only [gap]
  have Plo : 1/3<P2 d t := by dsimp [P2]; nlinarith only [small.1,small.2,dtcap,sq_nonneg t]
  have decreasing := second_order en (show Normal 1 0 by norm_num [Normal])
    shallow (by norm_num) en.1
  have Phi : P2 d t≤13/20 := by simpa [P2] using decreasing.1
  have Qhi : Q2 d t≤-1 := by simpa [Q2] using decreasing.2
  have Qlo : -1-t≤Q2 d t := by dsimp [Q2]; nlinarith only [dt,sq_nonneg t]
  have Rpos : 0<1-(61/100)*d-(13/20)*t := by linarith only [eb.2.1,small.2]
  exact ⟨pn,ph,Sn,Sh,SP,Plo,Phi,Qlo,Qhi,Rpos⟩

theorem support_join_identity (d t h r : ℝ) (en : Normal d t) :
    (P2 d t*h+Q2 d t*r)-(-P d t*h-Q d t*r)=
      -deltaE d t h r*(1-(7/20)*d+(9/100)*t) := by
  dsimp [P2,Q2,P,Q,deltaE]
  linear_combination (7/20)*h*en.2.2

theorem FE_lower_formula (d t h r : ℝ) (en : Normal d t)
    (order : deltaE d t h r≤0) : FE d t h r=-P d t*h-Q d t*r := by
  by_cases branch : 0≤deltaE d t h r
  · have zero : deltaE d t h r=0 := le_antisymm order branch
    rw [FE,if_pos branch]
    have identity := support_join_identity d t h r en
    rw [zero,neg_zero,zero_mul] at identity
    linarith only [identity]
  · rw [FE,if_neg branch]

theorem FE_upper_formula (d t h r : ℝ) (order : 0≤deltaE d t h r) :
    FE d t h r=P2 d t*h+Q2 d t*r := by rw [FE,if_pos order]

theorem FE_aligned (d t : ℝ) (en : Normal d t) : FE d t t d=E0 d t := by
  have zero : deltaE d t t d=0 := by dsimp [deltaE]; ring
  rw [FE,zero,if_pos (by norm_num : (0:ℝ)≤0)]
  dsimp [P2,Q2,E0]
  linear_combination (61/100)*t*en.2.2

end
end N12Compact.C1092MPPMNegativeCrosspointSupport
