import Compact.Completion.C1092.MPPMInwardFinalScalars
import Compact.Completion.CommonCases.CanonicalProjection

/-! The common successor comparisons in the two inward-final chapters.
The coefficient monotonicity is an exact chord identity, and the second
normal uses the existing unit-circle projection theorem. No angle grid
or differential estimate is a premise. -/
namespace N12Compact.C1092MPPMInwardFinal
open C977CornerCubic C1092WallProfileScalars CommonCases.CanonicalProjection
set_option Elab.async false
noncomputable section

def alpha (beta c s : ℝ) : ℝ := 1-c+beta*s
def P (d t : ℝ) : ℝ := 2-d-t+(49/85)*d*t
def Q (beta d t : ℝ) : ℝ := d-t+36/85-beta+(49/85)*t^2
def FC (beta c s d t : ℝ) : ℝ :=
  alpha beta c s+(c*d+s*t)*(1-d-t)+(c*t-s*d)*(1-t+(36/85)*d)
def FE (beta h c s d t : ℝ) : ℝ :=
  1-d-t+(c*d+s*t)*alpha beta c s+(c*t-s*d)*(1-h)

theorem FC_formula (beta c s d t : ℝ) (unit : d^2+t^2=1) :
    FC beta c s d t=1-c*P d t-s*Q beta d t := by
  dsimp [FC,alpha,P,Q]
  linear_combination -(c+(36/85)*s)*unit

theorem FE_formula (beta h c s d t : ℝ) :
    FE beta h c s d t=
      1-(1+(1-h)*s-c*alpha beta c s)*d-
        (1-(1-h)*c-s*alpha beta c s)*t := by
  dsimp [FE]
  ring

theorem coordinates_after {d t d0 t0 : ℝ} (dn : Normal d t) (en : Normal d0 t0)
    (cross : t0*d≤d0*t) : d≤d0 ∧ t0≤t := by
  have db := normal_bounds dn
  have eb := normal_bounds en
  have cosine := after d t d0 t0 1 0 dn.2.2 en.2.2 cross
    (by linarith only [en.1]) (by linarith only [eb.1])
  have dc : d≤d0 := by simpa using cosine
  have sine : t0≤t := by
    apply le_of_not_gt
    intro no
    have first := mul_nonneg (sub_nonneg.mpr dc)
      (show 0≤d0+d by linarith only [db.1,eb.1])
    have last := mul_pos (sub_pos.mpr no)
      (show 0<t0+t by linarith only [dn.1,no])
    nlinarith only [first,last,dn.2.2,en.2.2]
  exact ⟨dc,sine⟩

theorem coefficients_after (beta : ℝ) {d t d0 t0 : ℝ}
    (dn : Normal d t) (en : Normal d0 t0) (cross : t0*d≤d0*t) :
    P d t≤P d0 t0 ∧ Q beta d t≤Q beta d0 t0 := by
  have db := normal_bounds dn
  have eb := normal_bounds en
  have order := coordinates_after dn en cross
  let D := d+d0
  let T := t+t0
  let dc := d0-d
  let dt := t-t0
  have Dp : 0<D := by dsimp [D]; linarith only [db.1,eb.1]
  have dn' : 0≤dc := sub_nonneg.mpr order.1
  have tn' : 0≤dt := sub_nonneg.mpr order.2
  have balance : dc*D=dt*T := by dsimp [dc,dt,D,T]; nlinarith only [dn.2.2,en.2.2]
  have diagonal : 0≤D-T := by dsimp [D,T]; linarith only [dn.2.1,en.2.1]
  have bracket : 0≤1-(49/170)*(D+T) := by
    dsimp [D,T]
    linarith only [db.2.2.2.2.2,eb.2.2.2.2.2]
  have product := mul_nonneg (mul_nonneg tn' diagonal) bracket
  have firstIdentity : D*(P d t-P d0 t0)= -dt*(D-T)*(1-(49/170)*(D+T)) := by
    calc
      _ = dc*D*(1-(49/170)*T)-dt*D*(1-(49/170)*D) := by
        dsimp [P,dc,dt,D,T]; ring
      _ = _ := by rw [balance]; ring
  have first : P d t≤P d0 t0 := by
    apply le_of_not_gt
    intro no
    have positive := mul_pos Dp (sub_pos.mpr no)
    rw [firstIdentity] at positive
    nlinarith only [positive,product]
  have tcap : T≤10/7 := by
    dsimp [T]
    linarith only [dn.2.1,en.2.1,db.2.2.2.2.2,eb.2.2.2.2.2]
  have second := mul_nonpos_of_nonneg_of_nonpos tn'
    (show -1+(49/85)*T≤0 by linarith only [tcap])
  have secondIdentity : Q beta d t-Q beta d0 t0= -dc+dt*(-1+(49/85)*T) := by
    dsimp [Q,dc,dt,T]; ring
  exact ⟨first,by rw [←sub_nonpos]; rw [secondIdentity]; linarith only [dn',second]⟩

theorem FC_after (beta : ℝ) {c s d t d0 t0 : ℝ}
    (cn : Normal c s) (dn : Normal d t) (en : Normal d0 t0)
    (cross : t0*d≤d0*t) : FC beta c s d0 t0≤FC beta c s d t := by
  have bounds := coefficients_after beta dn en cross
  have first := mul_le_mul_of_nonneg_left bounds.1
    (by linarith only [(normal_bounds cn).1] : 0≤c)
  have last := mul_le_mul_of_nonneg_left bounds.2 cn.1
  rw [FC_formula _ _ _ _ _ dn.2.2,FC_formula _ _ _ _ _ en.2.2]
  linarith only [first,last]

/-- A uniform endpoint projection valid for both small inward domains
and both beta values. The height may be zero or the sharper centered h. -/
theorem FE_after {beta h c s d t d0 t0 : ℝ}
    (cn : Normal c s) (dn : Normal d t) (en : Normal d0 t0)
    (close : 49/50≤c) (small : s≤1/5)
    (betaLow : 0≤beta) (betaHigh : beta≤1/2)
    (heightLow : 0≤h) (heightHigh : h≤1/10)
    (endpointCosine : 4/5≤d0) (endpointSine : 19/50≤t0)
    (cross : t0*d≤d0*t) : FE beta h c s d0 t0≤FE beta h c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  let a := alpha beta c s
  let A := 1+(1-h)*s-c*a
  let B := 1-(1-h)*c-s*a
  have bn := mul_nonneg betaLow cn.1
  have bu := mul_le_mul_of_nonneg_right betaHigh cn.1
  have an : 0≤a := by dsimp [a,alpha]; linarith only [cb.2.1,bn]
  have au : a≤3/25 := by dsimp [a,alpha]; nlinarith only [close,small,bu]
  have ca := mul_le_mul_of_nonneg_right cb.2.1 an
  have sa := mul_le_mul_of_nonneg_left au cn.1
  have hs := mul_nonneg (show 0≤1-h by linarith only [heightHigh]) cn.1
  have hc := mul_le_mul_of_nonneg_right heightHigh
    (show 0≤c by linarith only [cb.1])
  have A_low : 22/25≤A := by dsimp [A]; nlinarith only [hs,ca,au]
  have B_high : B≤3/25 := by
    have nonnegative := mul_nonneg cn.1 an
    dsimp [B]
    nlinarith only [nonnegative,hc,cb.2.1,close]
  have B_low : -(3/125)≤B := by
    have product := mul_nonneg heightLow (show 0≤c by linarith only [cb.1])
    dsimp [B]
    nlinarith only [product,cb.2.1,sa,small]
  have first := mul_le_mul_of_nonneg_right B_high
    (show 0≤d0 by linarith only [eb.1])
  have last := mul_le_mul_of_nonneg_right A_low en.1
  have derivative : B*d0≤A*t0 := by
    nlinarith only [first,last,eb.2.1,endpointSine]
  have radial1 := mul_le_mul_of_nonneg_right A_low
    (show 0≤d0 by linarith only [eb.1])
  have radial2 := mul_le_mul_of_nonneg_right B_low en.1
  have value : 0≤A*d0+B*t0 := by
    nlinarith only [radial1,radial2,endpointCosine,eb.2.2.2.1]
  have projection := after d t d0 t0 A B dn.2.2 en.2.2 cross derivative value
  rw [FE_formula,FE_formula]
  change A*d+B*t≤A*d0+B*t0 at projection
  dsimp [A,B,a] at projection
  linarith only [projection]

end
#print axioms coefficients_after
#print axioms FE_after
end N12Compact.C1092MPPMInwardFinal
