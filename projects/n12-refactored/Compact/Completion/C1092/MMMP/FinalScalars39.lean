import Compact.Completion.C1092.MMMMPairScalars
import Compact.Completion.C1092.WallProfileScalars

/-! The final MMMP scalar contradictions using only the universal strict
left-wall endpoint2.39. The auxiliary pointG1 is unnecessary. All bounds
hold on the full canonical intervals and use exact unit-circle identities. -/
namespace N12Compact.C1092MMMPFinalScalars39
open C977CornerCubic C1092MMMMPairScalars
set_option Elab.async false
noncomputable section

private theorem short {d r x y : ℝ} (unit : d^2+r^2=1)
    (length : x^2+y^2 < 1) : x*d+y*r < 1 := by
  have identity : (x*d+y*r)^2+(x*r-y*d)^2=x^2+y^2 := by
    linear_combination (x^2+y^2)*unit
  nlinarith only [identity,length,sq_nonneg (x*r-y*d),sq_nonneg (x*d+y*r-1)]

def ownMargin (d r b t : ℝ) : ℝ :=
  1-d+(39/100)*r-(b*d+t*r)*(b+t-1)+(t*d-b*r)*(1+(39/100)*b-t)

def neighborMargin (d r b t : ℝ) : ℝ :=
  1-b-t+(b*d+t*r)*(1-d+(39/100)*r)+
    (t*d-b*r)*(1-(7/20)*d+(7/20)*r)

theorem own_positive {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (steep : 3/5 ≤ t) : 0 < ownMargin d r b t := by
  have bb := normal_bounds bn
  have tn := sine_bound bn
  have t2 : 9/25 ≤ t^2 := by
    have product := mul_nonneg (sub_nonneg.mpr steep)
      (show 0≤t+3/5 by linarith only [bn.1])
    nlinarith only [product]
  have th : t^2 ≤ 1/2 := by
    have product := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤b+t by linarith only [bb.1,bn.1])
    nlinarith only [product,bn.2.2]
  have arc := mul_nonneg (show 0≤t^2-9/25 by linarith only [t2])
    (show 0≤16/25-t^2 by linarith only [th])
  have weighted := congrArg (fun z : ℝ => z*t^2) bn.2.2
  dsimp at weighted
  have bt : 12/25 ≤ b*t := by
    have cross := mul_nonneg (by linarith only [bb.1] : 0≤b) bn.1
    nlinarith only [arc,weighted,cross,sq_nonneg (b*t-12/25)]
  have sum : 7/5 ≤ b+t := by
    nlinarith only [bt,bn.2.2,bb.2.2.2.2.1,sq_nonneg (b+t-7/5)]
  have bu : b ≤ 4/5 := by nlinarith only [bn.2.2,t2,sq_nonneg (b-4/5)]
  let K := 2-b-t+(3/5)*b*t
  let L := b-t+(3/5)*t^2
  have Kn : 0 ≤ K := by
    dsimp [K]
    nlinarith only [bb.2.2.2.2.2,mul_nonneg (by linarith only [bb.1] : 0≤b) bn.1]
  have Ln : 0 ≤ L := by dsimp [L]; nlinarith only [bn.2.1,sq_nonneg t]
  have curve := mul_nonpos_of_nonneg_of_nonpos (show 0≤b+t-7/5 by linarith only [sum])
    (show (3/10)*(b+t+7/5)-1≤0 by linarith only [bb.2.2.2.2.2])
  have identity : K-111/125=(b+t-7/5)*((3/10)*(b+t+7/5)-1) := by
    dsimp [K]
    linear_combination -(3/10)*bn.2.2
  have Ku : K ≤ 111/125 := by nlinarith only [curve,identity]
  have curveL := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr steep)
    (show (3/5)*(t+3/5)-1≤0 by linarith only [tn])
  have Lu : L ≤ 52/125 := by dsimp [L]; nlinarith only [curveL,bu]
  let K1 := K+(1/100)*b*t
  let L1 := L+(1/100)*t^2
  have btHigh : b*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (b-t)]
  have K1n : 0≤K1 := by
    dsimp [K1]
    nlinarith only [Kn,mul_nonneg (by linarith only [bb.1] : 0≤b) bn.1]
  have L1n : 0≤L1 := by dsimp [L1]; nlinarith only [Ln,sq_nonneg t]
  have K1u : K1≤893/1000 := by dsimp [K1]; nlinarith only [Ku,btHigh]
  have L1u : L1≤421/1000 := by dsimp [L1]; nlinarith only [Lu,th]
  have boundK := mul_nonneg (sub_nonneg.mpr K1u)
    (show 0≤893/1000+K1 by linarith only [K1n])
  have boundL := mul_nonneg (sub_nonneg.mpr L1u)
    (show 0≤421/1000+L1 by linarith only [L1n])
  have bound : K1^2+L1^2 < 1 := by nlinarith only [boundK,boundL]
  have projection := short dn.2.2 bound
  have decomposition : ownMargin d r b t=1-K1*d-L1*r := by
    dsimp [ownMargin,K1,L1,K,L]
    linear_combination (-d-(39/100)*r)*bn.2.2
  rw [decomposition]
  linarith only [projection]

private def K (d r : ℝ) : ℝ := 2-d+r-(13/20)*r^2-(37/50)*d*r
private def L (d r : ℝ) : ℝ := 27/20-d-r-(37/50)*r^2+(13/20)*d*r

private theorem coefficient_bounds {d r : ℝ} (dn : Normal d r) :
    1 ≤ K d r ∧ L d r ≤ 7/20 := by
  have db := normal_bounds dn
  have small := short (x:=3/4) (y:=13/20) dn.2.2 (by norm_num)
  have first := mul_nonneg dn.1 (show 0≤1-(3/4)*d-(13/20)*r by linarith only [small])
  have cross := mul_nonneg (by linarith only [db.1] : 0≤d) dn.1
  have last := mul_nonpos_of_nonneg_of_nonpos cross
    (show (13/20)*(1+d+r)-2≤0 by linarith only [db.2.2.2.2.2])
  have identity : (1+d+r)*(1-d-r+(13/20)*d*r)=
      d*r*((13/20)*(1+d+r)-2) := by linear_combination -dn.2.2
  have negative := nonpos_of_mul_nonpos_right (by rw [identity]; exact last)
    (show 0<1+d+r by linarith only [db.2.2.2.2.1])
  constructor
  · dsimp [K]; nlinarith only [first,db.2.1,cross]
  · dsimp [L]; nlinarith only [negative,sq_nonneg r]

private theorem endpoint_positive {d r : ℝ} (dn : Normal d r) :
    0 < 1-(275/373)*K d r-(252/373)*L d r := by
  have db := normal_bounds dn
  let w := C1092WallProfileScalars.half d r
  have hw := C1092WallProfileScalars.quarter_data d r
    (by linarith only [db.1]) dn.1 dn.2.2
  have denominator : 0 < 1+d := by linarith only [db.1]
  have wu : w ≤ 1/2 := (div_le_iff₀ denominator).mpr (by linarith only [dn.2.1,db.2.2.2.1])
  have wp : 0 < 1+w^2 := by nlinarith only [sq_nonneg w]
  have df : d=(1-w^2)/(1+w^2) := (eq_div_iff wp.ne').mpr (by nlinarith only [hw.2.2.2.1])
  have rf : r=2*w/(1+w^2) := (eq_div_iff wp.ne').mpr (by nlinarith only [hw.2.2.2.2])
  have w2 : w^2 ≤ 1/4 := by
    have product := mul_nonneg (show 0≤1/2-w by linarith only [wu])
      (show 0≤1/2+w by dsimp [w]; linarith only [hw.1])
    nlinarith only [product]
  have bracket : 0 < 42652-12540*w-104420*w^2 := by linarith only [wu,w2]
  have last := mul_nonneg (sq_nonneg w) bracket.le
  have numerator : 0 < 980+3340*w+w^2*(42652-12540*w-104420*w^2) := by
    dsimp [w] at last ⊢
    linarith only [last,hw.1]
  have identity : 100*373*(1+w^2)^2*(1-(275/373)*K d r-(252/373)*L d r)=
      980+3340*w+w^2*(42652-12540*w-104420*w^2) := by
    rw [df,rf]
    dsimp [K,L]
    field_simp [wp.ne']
    <;> ring
  have scaled : 0 < 100*373*(1+w^2)^2*(1-(275/373)*K d r-(252/373)*L d r) := by
    rwa [identity]
  apply lt_of_not_ge
  intro no
  have nonpositive := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤100*373*(1+w^2)^2 by positivity) no
  linarith only [scaled,nonpositive]

theorem neighbor_positive {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (steep : 252/373 ≤ t) : 0 < neighborMargin d r b t := by
  have bb := normal_bounds bn
  have projection := coefficient_bounds dn
  have endpoint := endpoint_positive dn
  have t2 := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤t+252/373 by linarith only [bn.1])
  have bu : b ≤ 275/373 := by nlinarith only [bn.2.2,t2,sq_nonneg (b-275/373)]
  have weight := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr steep)
    (show (7/20)*(b+275/373)-(t+252/373)≤0 by linarith only [bu,steep])
  have identity : (b+275/373)*((b-275/373)+(7/20)*(t-252/373))=
      (t-252/373)*((7/20)*(b+275/373)-(t+252/373)) := by
    linear_combination bn.2.2
  have order := nonpos_of_mul_nonpos_right (by rw [identity]; exact weight)
    (show 0<b+275/373 by linarith only [bb.1])
  have first := mul_nonpos_of_nonneg_of_nonpos (show 0≤K d r-1 by linarith only [projection.1])
    (show b-275/373≤0 by linarith only [bu])
  have last := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr steep)
    (show L d r-7/20≤0 by linarith only [projection.2])
  have comparison : b*K d r+t*L d r ≤ (275/373)*K d r+(252/373)*L d r := by
    nlinarith only [first,last,order]
  have decomposition : neighborMargin d r b t=1-b*K d r-t*L d r := by
    dsimp [neighborMargin,K,L]
    linear_combination (-b-(7/20)*t)*dn.2.2
  rw [decomposition]
  linarith only [comparison,endpoint]

#print axioms own_positive
#print axioms neighbor_positive
end
end N12Compact.C1092MMMPFinalScalars39
