import Compact.Completion.C1092.MPPMNegativeCrosspointG01Quartic

/-! NEGATIVE-WALL-SCALARS §7, the complete G01 boundary mode. Both
successor support signs and their common endpoint are included. The
first quartic interval is extended to 5/12 with a rational positive
endpoint, avoiding the algebraic endpoint sqrt(2)-1. The final interval
uses the manuscript's exact four Bernstein lower bounds. Source only. -/
namespace N12Compact.C1092MPPMNegativeCrosspointSupport
open C977CornerCubic C1092WallProfileScalars G01Quartic
set_option Elab.async false
noncomputable section

private theorem central_order (c s h r : ℝ) (cn : Normal c s)
    (q : Quarter h r) (order : h≤r) : 0≤deltaC c s h r := by
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1) q.sine
  have last := mul_nonneg cn.1 (sub_nonneg.mpr order)
  dsimp [deltaC]
  nlinarith only [first,last]

private theorem first_formula (c s d t h r : ℝ) (cn : Normal c s)
    (en : Normal d t) (q : Quarter h r) (order : h≤r)
    (branch : deltaE d t h r≤0) :
    G01 c s d t h r=(c-s)*h^2+(c+s)*h*r+s-
      (2*c+s-1-s*P d t)*h-s*(2-Q d t)*r := by
  unfold G01
  rw [abs_of_nonneg (central_order c s h r cn q order),FE_lower_formula d t h r en branch]
  dsimp [kC,deltaC,C0]
  linear_combination (s/2)*q.unit

private theorem second_formula (c s d t h r : ℝ) (cn : Normal c s)
    (q : Quarter h r) (order : h≤r) (branch : 0≤deltaE d t h r) :
    G01 c s d t h r=(c-s)*h^2+(c+s)*h*r+s-
      (2*c+s-1+s*P2 d t)*h-s*(2+Q2 d t)*r := by
  unfold G01
  rw [abs_of_nonneg (central_order c s h r cn q order),FE_upper_formula d t h r branch]
  dsimp [kC,deltaC,C0]
  linear_combination (s/2)*q.unit

private theorem aligned (c s d t : ℝ) (en : Normal d t) :
    G01 c s d t t d=G00 c s d t t d := by
  have kc : kC c s t d=ell c s d t := rfl
  have ke : kE d t t d=1 := by dsimp [kE]; nlinarith only [en.2.2]
  have de : deltaE d t t d=0 := by dsimp [deltaE]; ring
  unfold G01 G00 width
  rw [FE_aligned d t en,kc,ke,de]
  norm_num <;> ring

private theorem aligned_endpoint (c s d t A B : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (formula : G01 c s d t t d=(c-s)*t^2+(c+s)*t*d+s-A*t-B*d) :
    0≤T c s A B (half d t) := by
  have eb := normal_bounds en
  have q : Quarter t d := ⟨en.1,by linarith only [eb.1],by nlinarith only [en.2.2]⟩
  have point := G00_nonnegative cn en steep shallow q
  rw [←aligned c s d t en,formula] at point
  rw [parameter_identity c s A B t d q]
  exact mul_nonneg (sq_nonneg _) point

private theorem first_interval (c s d t z : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (low : half d t≤z) (high : z≤5/12) :
    0≤T c s (2*c+s-1-s*P d t) (s*(2-Q d t)) z := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have bounds := coefficient_bounds en shallow
  have sb := G01Quartic.steep_bounds cn steep
  let A := 2*c+s-1-s*P d t
  let B := s*(2-Q d t)
  have pn := mul_nonneg cn.1 bounds.1
  have ph := mul_le_mul_of_nonneg_left bounds.2.1 cn.1
  have Sn := mul_nonneg cn.1 bounds.2.2.1
  have Sh := mul_le_mul_of_nonneg_left bounds.2.2.2.1 cn.1
  have SP := mul_le_mul_of_nonneg_left bounds.2.2.2.2.1 cn.1
  have Bleft : s≤B := by dsimp [B]; nlinarith only [Sn]
  have Bn : 0≤B := le_trans cn.1 Bleft
  have sumcap : A+B≤2*(c+s)-1 := by dsimp [A,B]; nlinarith only [SP]
  have a0 : s-B≤0 := by linarith only [Bleft]
  have a1 : 0≤2*(c+s-A) := by dsimp [A]; nlinarith only [pn,sb.1]
  have a4 : 0≤s+B := add_nonneg cn.1 Bn
  have a4cap : s+B≤2 := by dsimp [B]; nlinarith only [Sh,sb.2.1]
  have sumlo : 2≤c+s+A := by dsimp [A]; nlinarith only [ph,cb.1,steep]
  have curvature : 0≤-(-2*(c+s+A))-3*(5/12)*(s+B) := by
    linarith only [sumlo,a4cap]
  have wdata := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  have wcap := half_bound en shallow
  have endpoint := aligned_endpoint c s d t A B cn steep en shallow
    (first_formula c s d t t d cn en
      ⟨en.1,by linarith only [eb.1],by nlinarith only [en.2.2]⟩ en.2.1
      (by dsimp [deltaE]; nlinarith))
  have right : 0≤T c s A B (5/12) := by
    have weight := mul_le_mul_of_nonneg_right sumcap
      (show (0:ℝ)≤120/169 by norm_num)
    have extra := mul_le_mul_of_nonneg_right Bleft
      (show (0:ℝ)≤1/169 by norm_num)
    have comparison : 120/169-(21/50)*(c+s)≤
        (c-s)*(120/169)^2+(c+s)*(120/169)*(119/169)+s-
          A*(120/169)-B*(119/169) := by
      nlinarith only [weight,extra,cb.1,cn.1]
    have strict : 0<(c-s)*(120/169)^2+(c+s)*(120/169)*(119/169)+s-
        A*(120/169)-B*(119/169) := by
      linarith only [comparison,cb.2.2.2.2.2]
    have identity : T c s A B (5/12)=(1+(5/12:ℝ)^2)^2*
        ((c-s)*(120/169)^2+(c+s)*(120/169)*(119/169)+s-
          A*(120/169)-B*(119/169)) := by dsimp [T,poly]; ring
    rw [identity]
    positivity
  exact endpoints (s-B) (2*(c+s-A)) (4*c-2*s) (-2*(c+s+A)) (s+B)
    (half d t) (5/12) z (by norm_num) wdata.1 (by linarith only [wcap])
    low high a0 a1 a4 curvature endpoint right

private theorem last_interval (c s d t z : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (zn : 0≤z) (high : z≤half d t) :
    0≤T c s (2*c+s-1+s*P2 d t) (s*(2+Q2 d t)) z := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have bounds := coefficient_bounds en shallow
  have sb := G01Quartic.steep_bounds cn steep
  let A := 2*c+s-1+s*P2 d t
  let B := s*(2+Q2 d t)
  let w := half d t
  let a0 := s-B
  let a1 := 2*(c+s-A)
  let a2 := 4*c-2*s
  let a3 := -2*(c+s+A)
  let a4 := s+B
  let gap := 1/3-P2 d t
  have wn : 0≤w := (quarter_data d t (by linarith only [eb.1]) en.1 en.2.2).1
  have endpoint := aligned_endpoint c s d t A B cn steep en shallow
    (second_formula c s d t t d cn
      ⟨en.1,by linarith only [eb.1],by nlinarith only [en.2.2]⟩ en.2.1
      (by dsimp [deltaE]; nlinarith))
  by_cases zero : w=0
  · have eq : z=w := by linarith only [zn,high,zero]
    simpa only [eq] using endpoint
  have wp : 0<w := lt_of_le_of_ne wn (Ne.symm zero)
  have gapn : s*gap≤0 := mul_nonpos_of_nonneg_of_nonpos cn.1
    (by dsimp [gap]; linarith only [bounds.2.2.2.2.2.1])
  have a1low : 2*s*gap≤a1 := by
    dsimp [a1,A,gap]
    linarith only [sb.2.2]
  have a2n : 0≤a2 := by dsimp [a2]; linarith only [cn.2.1,cb.1]
  have Pcap := mul_le_mul_of_nonneg_left bounds.2.2.2.2.2.2.1 cn.1
  have a3low : -(21/2)*s≤a3 := by
    have ratio : 3*c≤4*s := by linarith only [sb.1,steep]
    dsimp [a3,A]
    nlinarith only [ratio,Pcap,sb.2.1]
  have a0identity : a0=s*t*(1-(61/100)*d-(13/20)*t) := by
    dsimp [a0,B,Q2]
    ring
  have base : 0≤a0+(3/2)*s*gap*w-(21/8)*s*w^3 := by
    have weighted := mul_nonneg cn.1 (lower_coefficient d t en shallow)
    rw [a0identity]
    dsimp [gap,w] at weighted ⊢
    nlinarith only [weighted]
  have gapweight := mul_nonpos_of_nonpos_of_nonneg gapn wn
  have cube := mul_nonneg cn.1 (pow_nonneg wn 3)
  have b0 : 0≤a0 := by nlinarith only [base,gapweight,cube]
  have first := mul_nonneg (show 0≤a1/4-(3/2)*s*gap by linarith only [a1low,gapn]) wn
  have b1 : 0≤a0+a1*w/4 := by nlinarith only [base,first,cube]
  have second := mul_nonneg (show 0≤a1/2-(3/2)*s*gap by linarith only [a1low,gapn]) wn
  have square := mul_nonneg a2n (sq_nonneg w)
  have b2 : 0≤a0+a1*w/2+a2*w^2/6 := by nlinarith only [base,second,square,cube]
  have third := mul_nonneg (show 0≤3*a1/4-(3/2)*s*gap by linarith only [a1low]) wn
  have fourth := mul_nonneg (show 0≤a3/4+(21/8)*s by linarith only [a3low])
    (pow_nonneg wn 3)
  have b3 : 0≤a0+3*a1*w/4+a2*w^2/2+a3*w^3/4 := by
    nlinarith only [base,third,square,fourth]
  exact bernstein a0 a1 a2 a3 a4 w z wp zn high b0 b1 b2 b3 endpoint

/-- Complete required range of NEGATIVE-WALL-SCALARS G01, including
beta=pi/4, beta=Theta, beta=pi/2, q=0 and 8t=3d. -/
theorem G01_nonnegative (c s d t h r : ℝ) (cn : Normal c s)
    (steep : 3/5≤s) (en : Normal d t) (shallow : 8*t≤3*d)
    (q : Quarter h r) (order : h≤r) : 0≤G01 c s d t h r := by
  let z := half r h
  let w := half d t
  have eb := normal_bounds en
  have bd := quarter_data r h q.sine q.cosine (by nlinarith only [q.unit])
  have ed := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  have zn : 0≤z := bd.1
  have wn : 0≤w := ed.1
  have zp : 0<1+z^2 := by positivity
  have wp : 0<1+w^2 := by positivity
  have factor : 0<2*(1+w*z) := by have product := mul_nonneg wn zn; linarith only [product]
  have identity := parameter_order d t h r en q
  change (1+w^2)*(1+z^2)*deltaE d t h r=2*(w-z)*(1+w*z) at identity
  by_cases branch : 0≤deltaE d t h r
  · have weighted := mul_nonneg (mul_nonneg wp.le zp.le) branch
    rw [identity,show 2*(w-z)*(1+w*z)=(w-z)*(2*(1+w*z)) by ring] at weighted
    have gap := nonneg_of_mul_nonneg_left weighted factor
    have zw : z≤w := by linarith only [gap]
    have proof := last_interval c s d t z cn steep en shallow zn zw
    rw [parameter_identity c s (2*c+s-1+s*P2 d t) (s*(2+Q2 d t)) h r q,
      ←second_formula c s d t h r cn q order branch] at proof
    exact nonneg_of_mul_nonneg_right proof (sq_pos_of_pos zp)
  · have branch : deltaE d t h r≤0 := (lt_of_not_ge branch).le
    have weighted := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg wp.le zp.le) branch
    rw [identity,show 2*(w-z)*(1+w*z)=(w-z)*(2*(1+w*z)) by ring] at weighted
    have gap := nonpos_of_mul_nonpos_left weighted factor
    have wz : w≤z := by linarith only [gap]
    have proof := first_interval c s d t z cn steep en shallow wz (parameter_bound q order)
    rw [parameter_identity c s (2*c+s-1-s*P d t) (s*(2-Q d t)) h r q,
      ←first_formula c s d t h r cn en q order branch] at proof
    exact nonneg_of_mul_nonneg_right proof (sq_pos_of_pos zp)

#print axioms G01_nonnegative
end
end N12Compact.C1092MPPMNegativeCrosspointSupport
