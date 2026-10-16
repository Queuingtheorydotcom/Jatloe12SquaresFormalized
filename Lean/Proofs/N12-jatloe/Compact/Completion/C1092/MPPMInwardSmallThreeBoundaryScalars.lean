import Compact.Completion.C1092.MPPMInwardSmallThreeBottom

/-! Rational margins for every actual B--E source in the small-inward
ending. These estimates apply after the two actual-pair reductions;
they do not replace either square by independent support endpoints. -/
namespace N12Compact.C1092MPPMInwardSmallThree
open C977CornerCubic
set_option Elab.async false
noncomputable section

def nu (d t h k : ℝ) := d*h-t*k
def eta (d t h k : ℝ) := t*h+d*k
def X0 (d t : ℝ) := 1-d-t+(3/5)*d*t
def Y0 (d t : ℝ) := t-d-1+(3/5)*d^2
def Delta0 (d t : ℝ) := 1-t-(3/5)*d
def Z0 (d t h k : ℝ) := (49/100)*d*h+t*(1-(543/500)*h)-k*((49/100)*t+(543/500)*d)

structure BoundaryRange (d t h k : ℝ) : Prop where
  normal : Normal d t
  cosine : 15/17<d
  sineLow : 1/3<t
  sineHigh : t<8/17
  bottomCosine : 999/1000<h
  bottomUnit : h^2+k^2=1
  bottomLow : -(43/1000)<k
  bottomHigh : k<21/1000

theorem boundary_coefficients {d t h k : ℝ} (q : BoundaryRange d t h k) :
    0<nu d t h k ∧ nu d t h k≤1 ∧ 7/25<eta d t h k ∧ h≤1 := by
  have eb := normal_bounds q.normal
  have dp : 0<d := by linarith only [q.cosine]
  have tp : 0<t := by linarith only [q.sineLow]
  have hp : 0<h := by linarith only [q.bottomCosine]
  have hcap : h≤1 := by nlinarith only [q.bottomUnit,sq_nonneg k,sq_nonneg (h-1)]
  have first := mul_pos (show 0<d-22/25 by linarith only [q.cosine]) hp
  have second := mul_nonneg tp.le (show 0≤21/1000-k by linarith only [q.bottomHigh])
  have np : 0<nu d t h k := by
    dsimp [nu]
    nlinarith only [first,second,q.bottomCosine,q.sineHigh]
  have third := mul_pos (show 0<t-1/3 by linarith only [q.sineLow]) hp
  have fourth := mul_pos dp (show 0<k+43/1000 by linarith only [q.bottomLow])
  have reserve := mul_nonneg (show 0≤1-d by linarith only [eb.2.1]) (by norm_num : (0:ℝ)≤43/1000)
  have ep : 7/25<eta d t h k := by
    dsimp [eta]
    nlinarith only [third,fourth,reserve,q.bottomCosine]
  have unit : (nu d t h k)^2+(eta d t h k)^2=1 := by
    dsimp [nu,eta]
    linear_combination (h^2+k^2)*q.normal.2.2+q.bottomUnit
  exact ⟨np,by nlinarith only [unit,sq_nonneg (eta d t h k),sq_nonneg (nu d t h k-1)],ep,hcap⟩

theorem boundary_margins {d t h k : ℝ} (q : BoundaryRange d t h k)
    (width : 1<t+(343/500)*d) :
    X0 d t< -(1/17) ∧ 0<Y0 d t+543/500 ∧ Y0 d t+543/500<3/10 ∧ 0<Delta0 d t := by
  have eb := normal_bounds q.normal
  have dp : 0<d := by linarith only [q.cosine]
  have tp : 0<t := by linarith only [q.sineLow]
  have product := mul_pos (show 0<d-15/17 by linarith only [q.cosine]) tp
  have dt : 5/17<d*t := by nlinarith only [product,q.sineLow]
  have first := mul_neg_of_pos_of_neg (show 0<d*t by positivity)
    (show (4/5)*(1+d+t)-2<0 by linarith only [eb.2.2.2.2.2])
  have identity : (1+d+t)*(X0 d t+d*t/5)=d*t*((4/5)*(1+d+t)-2) := by
    dsimp [X0]
    linear_combination -q.normal.2.2
  have scaled : (1+d+t)*(X0 d t+d*t/5)<0 := by rw [identity]; exact first
  have xgap := neg_of_mul_neg_right scaled (show 0≤1+d+t by positivity)
  have ybase := mul_nonneg (show 0≤1-d by linarith only [eb.2.1])
    (show 0≤543/500-(3/5)*d by linarith only [eb.2.1])
  have square : d^2≤1 := by nlinarith only [q.normal.2.2,sq_nonneg t]
  have dlo : 0<Delta0 d t := by
    have first := mul_pos (show 0<8/17-t by linarith only [q.sineHigh])
      (show 0<1-t by linarith only [q.sineHigh])
    have identity : (1-t)^2-((3/5)*d)^2=(34/25)*(8/17-t)*(1-t) := by
      linear_combination -(9/25)*q.normal.2.2
    dsimp [Delta0]
    nlinarith only [first,identity,dp,sq_nonneg (1-t-(3/5)*d)]
  refine ⟨by nlinarith only [xgap,dt],?_,?_,dlo⟩
  · dsimp [Y0]
    nlinarith only [ybase,width]
  · dsimp [Y0]
    nlinarith only [q.sineHigh,q.cosine,square]

theorem first_source_margin {d t h k : ℝ} (q : BoundaryRange d t h k)
    (width : 1<t+(343/500)*d) : h*X0 d t+k*(Y0 d t+543/500)<0 := by
  have margins := boundary_margins q width
  have first := mul_neg_of_pos_of_neg (show 0<h by linarith only [q.bottomCosine])
    (show X0 d t+1/17<0 by linarith only [margins.1])
  have last := mul_pos (show 0<21/1000-k by linarith only [q.bottomHigh]) margins.2.1
  nlinarith only [first,last,q.bottomCosine,margins.2.2.1]

theorem positive_transverse_coefficient {d t h k : ℝ} (q : BoundaryRange d t h k)
    (kn : 0≤k) : 1/3<Z0 d t h k := by
  have eb := normal_bounds q.normal
  have hp : 0<h := by linarith only [q.bottomCosine]
  have coeff := boundary_coefficients q
  have first := mul_pos (show 0<d-22/25 by linarith only [q.cosine]) hp
  have second := mul_nonneg q.normal.1
    (show 0≤1-(543/500)*h+43/500 by linarith only [coeff.2.2.2])
  have fn : 0≤(49/100)*t+(543/500)*d := by
    have dp : 0≤d := by linarith only [q.cosine]
    exact add_nonneg (mul_nonneg (by norm_num) q.normal.1) (mul_nonneg (by norm_num) dp)
  have third := mul_nonneg (show 0≤21/1000-k by linarith only [q.bottomHigh]) fn
  dsimp [Z0]
  nlinarith only [first,second,third,q.bottomCosine,q.sineHigh,eb.2.1]

theorem negative_transverse_margin {d t h k : ℝ} (q : BoundaryRange d t h k)
    (negative : k<0) :
    0<d*(1-h)-(543/500)*d*k^2+(-k)*t*((543/500)*h-1) := by
  have eb := normal_bounds q.normal
  have coeff := boundary_coefficients q
  let l := -k
  have lp : 0<l := by dsimp [l]; linarith only [negative]
  have lu : l<43/1000 := by dsimp [l]; linarith only [q.bottomLow]
  have deficit : l^2/2≤1-h := by dsimp [l]; nlinarith only [q.bottomUnit,sq_nonneg (1-h)]
  have first := mul_nonneg (show 0≤d by linarith only [q.cosine]) (sub_nonneg.mpr deficit)
  have second := mul_nonneg (show 0≤1-d by linarith only [eb.2.1]) (sq_nonneg l)
  have last := mul_pos lp (show 0<43/1000-l by linarith only [lu])
  have base : 0<(543/500)*h-1 := by linarith only [q.bottomCosine]
  have third := mul_nonneg (show 0≤t-1/3 by linarith only [q.sineLow]) base.le
  have fourth := mul_nonneg lp.le
    (show 0≤t*((543/500)*h-1)-(1/3)*((543/500)*(999/1000)-1) by
      nlinarith only [third,q.bottomCosine])
  rw [show k^2=l^2 by dsimp [l]; ring]
  change 0<d*(1-h)-(543/500)*d*l^2+l*t*((543/500)*h-1)
  nlinarith only [first,second,last,fourth,lp]

theorem negative_relative_cosine {d t h k : ℝ} (q : BoundaryRange d t h k)
    (negative : k<0) : d≤nu d t h k := by
  have eb := normal_bounds q.normal
  have bn : Normal h (-k) := ⟨by linarith only [negative],
    by linarith only [q.bottomLow,q.bottomCosine],by nlinarith only [q.bottomUnit]⟩
  have first := mul_pos (show 0<t-1/3 by linarith only [q.sineLow])
    (show 0<h by linarith only [q.bottomCosine])
  have last := mul_nonneg (show 0≤1-d by linarith only [eb.2.1])
    (show 0≤-k by linarith only [negative])
  have order : (-k)*d≤h*t := by nlinarith only [first,last,q.bottomCosine,q.bottomLow]
  have bound := C1092MPPMInwardFinal.BottomAngle.relative_dot_lower bn q.normal order
  dsimp [nu]
  nlinarith only [bound]

end
end N12Compact.C1092MPPMInwardSmallThree
