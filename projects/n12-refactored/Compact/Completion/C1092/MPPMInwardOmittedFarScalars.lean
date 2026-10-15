import Compact.Completion.C1092.MPPMInwardOmittedFarBar
import Compact.Completion.C1092.MPPMNonpositivePredecessorScalars

/-! Whole-interval scalar comparisons for the omitted-G far ending.
Coefficient monotonicity and the quartic endpoint minimum are proved
by finite differences; no derivative, angle sample or grid is used. -/
namespace N12Compact.C1092MPPMInwardOmittedFar.Scalars
open C977CornerCubic C1092WallProfileScalars C1092MPPMInwardFinal
open CommonCases.CanonicalProjection
set_option Elab.async false
noncomputable section

def d0 : ℝ := 263000/319169
def t0 : ℝ := 180831/319169
def P (d t : ℝ) : ℝ := 2-d-t+(11/25)*d*t
def Q (d t : ℝ) : ℝ := d-t+4/25+(11/25)*t^2
def a (c s : ℝ) : ℝ := 1-c+(2/5)*s
def sourceGap (c s d t : ℝ) : ℝ :=
  a c s+(c*d+s*t)*(1-d-t)+(c*t-s*d)*(1-t+(14/25)*d)
def targetGap (c s d t : ℝ) : ℝ :=
  1-d-t+(c*d+s*t)*a c s+(c*t-s*d)*(108/125)
def N (x : ℝ) : ℝ :=
  -100862498*x^4+7307500*x^3+70750700*x^2-30508000*x+3946998

theorem endpoint : Normal d0 t0 := by norm_num [Normal,d0,t0]

theorem source_bounds {c s : ℝ} (cn : Normal c s) (small : half c s≤21/100) :
    91/100<c ∧ s<41/100 := by
  have base : Normal (9559/10441:ℝ) (4200/10441) := by norm_num [Normal]
  have baseHalf : half (9559/10441) (4200/10441)=(21:ℝ)/100 := by norm_num [half]
  have cross := half_cross cn base (by simpa only [baseHalf] using small)
  have coordinates := coordinates_after base cn cross
  constructor <;> linarith only [coordinates.1,coordinates.2]

theorem endpoint_order {d t : ℝ} (en : Normal d t) (large : 237/763≤half d t) :
    t0*d≤d0*t ∧ d≤d0 ∧ t0≤t := by
  have baseHalf : half d0 t0=(237:ℝ)/763 := by norm_num [half,d0,t0]
  have cross := half_cross endpoint en (by simpa only [baseHalf] using large)
  exact ⟨cross,coordinates_after en endpoint cross⟩

private theorem coefficients_after {d t : ℝ} (en : Normal d t)
    (cross : t0*d≤d0*t) : P d t≤P d0 t0 ∧ Q d t≤Q d0 t0 := by
  have eb := normal_bounds en
  have bb := normal_bounds endpoint
  have order := coordinates_after en endpoint cross
  let D := d+d0
  let T := t+t0
  let dc := d0-d
  let dt := t-t0
  have Dp : 0<D := by dsimp [D]; linarith only [eb.1,bb.1]
  have dn : 0≤dc := sub_nonneg.mpr order.1
  have tn : 0≤dt := sub_nonneg.mpr order.2
  have balance : dc*D=dt*T := by dsimp [dc,dt,D,T]; nlinarith only [en.2.2,endpoint.2.2]
  have diagonal : 0≤D-T := by dsimp [D,T]; linarith only [en.2.1,endpoint.2.1]
  have bracket : 0≤1-(11/50)*(D+T) := by
    dsimp [D,T]
    linarith only [eb.2.2.2.2.2,bb.2.2.2.2.2]
  have product := mul_nonneg (mul_nonneg tn diagonal) bracket
  have firstIdentity : D*(P d t-P d0 t0)= -dt*(D-T)*(1-(11/50)*(D+T)) := by
    calc
      _ = dc*D*(1-(11/50)*T)-dt*D*(1-(11/50)*D) := by
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
    linarith only [en.2.1,endpoint.2.1,eb.2.2.2.2.2,bb.2.2.2.2.2]
  have second := mul_nonpos_of_nonneg_of_nonpos tn
    (show -1+(11/25)*T≤0 by linarith only [tcap])
  have secondIdentity : Q d t-Q d0 t0= -dc+dt*(-1+(11/25)*T) := by
    dsimp [Q,dc,dt,T]; ring
  exact ⟨first,by nlinarith only [secondIdentity,dn,second]⟩

theorem source_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (large : 237/763≤half d t) : 0<sourceGap c s d t := by
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have order := endpoint_order en large
  have coefficients := coefficients_after en order.1
  have pcap : P d t<41/50 := lt_of_le_of_lt coefficients.1 (by norm_num [P,d0,t0])
  have qcap : Q d t<14/25 := lt_of_le_of_lt coefficients.2 (by norm_num [Q,d0,t0])
  have first := mul_lt_mul_of_pos_left pcap cp
  have last := mul_le_mul_of_nonneg_left qcap.le cn.1
  have norm := C1092MPPMNonpositivePredecessor.norm_lt (41/50) (14/25) c s 1
    cn.2.2 (by norm_num) (by norm_num)
  have identity : sourceGap c s d t=1-c*P d t-s*Q d t := by
    dsimp [sourceGap,a,P,Q]
    linear_combination -(c+(14/25)*s)*en.2.2
  rw [identity]
  linarith only [first,last,norm]

private theorem polynomial_lower {x : ℝ} (xn : 0≤x) (xu : x≤21/100) : 500000<N x := by
  have square := mul_nonneg (sub_nonneg.mpr xu) (show 0≤21/100+x by linarith only [xn])
  have mixed := mul_le_mul_of_nonneg_right xu (show (0:ℝ)≤21/100 by norm_num)
  have cubes : 0≤x^3+x^2*(21/100)+x*(21/100)^2 := by positivity
  let B := 30508000-70750700*(x+21/100)-7307500*(x^2+x*(21/100)+(21/100)^2)+
    100862498*(x^3+x^2*(21/100)+x*(21/100)^2+(21/100)^3)
  have Bn : 0≤B := by dsimp [B]; nlinarith only [xu,square,mixed,cubes]
  have product := mul_nonneg (sub_nonneg.mpr xu) Bn
  have identity : N x-N (21/100)=(21/100-x)*B := by dsimp [N,B]; ring
  have exactEndpoint : 500000<N (21/100) := by norm_num [N]
  nlinarith only [identity,product,exactEndpoint]

private theorem target_endpoint {c s : ℝ} (cn : Normal c s) (small : half c s≤21/100) :
    1/100<targetGap c s d0 t0 := by
  have cb := normal_bounds cn
  let x := half c s
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have xn : 0≤x := data.1
  have xu : x≤21/100 := small
  have den : 0<1+x^2 := by positivity
  have cform : c=(1-x^2)/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.1])
  have sform : s=2*x/(1+x^2) :=
    (eq_div_iff den.ne').mpr (by nlinarith only [data.2.2.2.2])
  have identity : 39896125*(1+x^2)^2*targetGap c s d0 t0=N x := by
    rw [cform,sform]
    dsimp [targetGap,a,N,d0,t0]
    field_simp [den.ne']
    <;> ring
  have value := polynomial_lower xn xu
  have square := mul_nonneg (sub_nonneg.mpr xu) (show 0≤21/100+x by linarith only [xn])
  have dh : 1+x^2≤21/20 := by nlinarith only [square]
  have denSquare := mul_nonneg (sub_nonneg.mpr dh)
    (show 0≤21/20+(1+x^2) by positivity)
  have denCap : 39896125*(1+x^2)^2<50000000 := by nlinarith only [denSquare]
  have scaled : 0<39896125*(1+x^2)^2*(targetGap c s d0 t0-1/100) := by
    nlinarith only [identity,value,denCap]
  have result := pos_of_mul_pos_right scaled (show 0≤39896125*(1+x^2)^2 by positivity)
  linarith only [result]

theorem target_positive {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (small : half c s≤21/100) (large : 237/763≤half d t) :
    1/100<targetGap c s d t := by
  have cb := normal_bounds cn
  have bounds := source_bounds cn small
  have order := endpoint_order en large
  let A := 1+(108/125)*s-c*a c s
  let B := 1-(108/125)*c-s*a c s
  have an : 0≤a c s := by dsimp [a]; linarith only [cb.2.1,cn.1]
  have au : a c s<13/50 := by dsimp [a]; linarith only [bounds.1,bounds.2]
  have ca := mul_le_mul_of_nonneg_right cb.2.1 an
  have sa := mul_le_mul_of_nonneg_left au.le cn.1
  have sn := mul_nonneg (show (0:ℝ)≤108/125 by norm_num) cn.1
  have An : 37/50<A := by dsimp [A]; linarith only [ca,au,sn]
  have product := mul_nonneg cn.1 an
  have Bh : B<11/50 := by dsimp [B]; linarith only [product,bounds.1]
  have Bn : 0≤B := by dsimp [B]; nlinarith only [sa,cb.2.1,bounds.2]
  have derivative : B*d0≤A*t0 := by
    have first := mul_le_mul_of_nonneg_right Bh.le (show 0≤d0 by norm_num [d0])
    have last := mul_le_mul_of_nonneg_right An.le (show 0≤t0 by norm_num [t0])
    dsimp [d0,t0] at first last ⊢
    linarith only [first,last]
  have radial : 0≤A*d0+B*t0 := by
    have first := mul_nonneg (show 0≤A by linarith only [An]) (show 0≤d0 by norm_num [d0])
    have last := mul_nonneg Bn (show 0≤t0 by norm_num [t0])
    linarith only [first,last]
  have comparison := after d t d0 t0 A B en.2.2 endpoint.2.2 order.1 derivative radial
  have formula (d t : ℝ) : targetGap c s d t=1-A*d-B*t := by
    dsimp [targetGap,A,B]
    ring
  have value := target_endpoint cn small
  rw [formula] at value ⊢
  linarith only [value,comparison]

end
end N12Compact.C1092MPPMInwardOmittedFar.Scalars
