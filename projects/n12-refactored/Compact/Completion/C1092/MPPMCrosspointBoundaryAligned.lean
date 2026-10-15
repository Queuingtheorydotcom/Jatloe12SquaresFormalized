import Compact.Completion.C1092.MPPMCrosspointBoundaryCoefficients
import Compact.Completion.C1092.MPPMCrosspointBoundaryG10Clamp
import Compact.Completion.C1092.MPPMCrosspointCentralAligned

/-! The strictly positive beta=p endpoint of BOUNDARY-SCALARS §3.
Finite unit-circle differences replace both monotonicity arguments;
the remaining low-angle endpoint is the manuscript's exact quartic. -/
namespace N12Compact.C1092MPPMCrosspointSupport
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false
noncomputable section

def alignedBoundary (c s d t : ℝ) : ℝ :=
  2*c+s-2-(543/500)*c*s-s*FE d t c s

private def alignedPoly (c s d t : ℝ) : ℝ :=
  2*c+s-2-(543/500+P d t)*c*s+Q d t*s^2

private theorem aligned_form {c s d t : ℝ}
    (cn : Normal c s) (en : Normal d t) (order : t≤s) :
    alignedBoundary c s d t=alignedPoly c s d t := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cross := CommonCases.UnitCircleChord.cross_order
    (show 0≤d by linarith only [eb.1]) (show 0≤c by linarith only [cb.1])
    en.2.2 cn.2.2 en.1 cn.1 order
  have form := FE_after en (show 0≤deltaE d t c s by exact cross)
  dsimp [alignedBoundary,alignedPoly]
  rw [form]
  ring

private theorem aligned_self {c s : ℝ} (cn : Normal c s) :
    alignedBoundary c s c s=Central.diagonalValue c s := by
  have support : FE c s c s=E0 c s := by
    simp only [FE,deltaE,show c*s-s*c=0 by ring,le_refl,if_true,zero_mul,sub_zero]
    dsimp [kE]
    linear_combination (E0 c s)*cn.2.2
  dsimp [alignedBoundary]
  rw [support]
  dsimp [E0,Central.diagonalValue]
  ring

private theorem polynomial_order {c s c₀ s₀ d t : ℝ}
    (cn : Normal c s) (base : Normal c₀ s₀) (en : Normal d t)
    (steep : 3/5≤s₀) (order : s₀≤s) :
    alignedPoly c₀ s₀ d t≤alignedPoly c s d t := by
  have cb := normal_bounds cn
  have bb := normal_bounds base
  have cs := steep_bounds cn (le_trans steep order)
  have bs := steep_bounds base steep
  have coeff := coefficient_bounds en
  let D := c+c₀
  let T := s+s₀
  let A := 543/500+P d t
  let J := D-2*T-(A/2)*(D^2-T^2)+Q d t*D*T
  have Dn : 0<D := by dsimp [D]; linarith only [cb.1,bb.1]
  have Tn : 0≤T := add_nonneg cn.1 base.1
  have TD : T≤D := by dsimp [T,D]; linarith only [cn.2.1,base.2.1]
  have square : 0≤D^2-T^2 := by
    have product := mul_nonneg (sub_nonneg.mpr TD) (by linarith only [Dn,Tn] : 0≤D+T)
    nlinarith only [product]
  have circle : D^2+T^2≤4 := by
    dsimp [D,T]
    nlinarith only [cn.2.2,base.2.2,sq_nonneg (c-c₀),sq_nonneg (s-s₀)]
  have sum : 14/5≤D+T := by dsimp [D,T]; linarith only [cs.2.2.1,bs.2.2.1]
  have aterm := mul_nonneg square (show 0≤1299/1000-A by dsimp [A]; linarith only [coeff.2.1])
  have qterm := mul_nonneg (mul_nonneg Dn.le Tn)
    (show 0≤Q d t-1 by linarith only [coeff.2.2.1])
  have chord := mul_nonneg (show 0≤D+T-14/5 by linarith only [sum])
    (show 0≤1+T by linarith only [Tn])
  have Jn : 0≤J := by
    dsimp [J]
    nlinarith only [aterm,qterm,chord,circle,sq_nonneg (T-100/299)]
  have identity : D*(alignedPoly c s d t-alignedPoly c₀ s₀ d t)=(s-s₀)*J := by
    dsimp [D,T,J,A,alignedPoly]
    linear_combination (-2+((543/500+P d t)/2)*(s+s₀))*base.2.2-
      (-2+((543/500+P d t)/2)*(s+s₀))*cn.2.2
  have product := mul_nonneg (sub_nonneg.mpr order) Jn
  rw [←identity] at product
  have result := nonneg_of_mul_nonneg_right product Dn
  linarith only [result]

private theorem low_endpoint {d t : ℝ} (en : Normal d t) (small : t≤3/5) :
    0<alignedPoly (4/5) (3/5) d t := by
  have eb := normal_bounds en
  have cosine : 4/5≤d := cosine_order (show Normal (4/5) (3/5) by norm_num [Normal]) en small
  let y := t/(1+d)
  let z := 1/3-y
  have denom : 0<1+d := by linarith only [eb.1]
  have yn : 0≤y := div_nonneg en.1 denom.le
  have yh : y≤1/3 := by
    apply (div_le_iff₀ denom).mpr
    linarith only [cosine,small]
  have zn : 0≤z := by dsimp [z]; linarith only [yh]
  have zh : z≤1/3 := by dsimp [z]; linarith only [yn]
  have relation : y*(1+d)=t := div_mul_cancel₀ _ denom.ne'
  have half : t*y=1-d := by
    apply mul_right_cancel₀ denom.ne'
    linear_combination t*relation+en.2.2
  have dh : d=(1-y^2)/(1+y^2) := by
    apply (eq_div_iff (by positivity : (1+y^2:ℝ)≠0)).mpr
    linear_combination y*relation+half
  have th : t=2*y/(1+y^2) := by
    apply (eq_div_iff (by positivity : (1+y^2:ℝ)≠0)).mpr
    linear_combination y*half-relation
  have identity : 12500*(1+y^2)^2*alignedPoly (4/5) (3/5) d t=
      400/81-(3760/27)*z+(22352/3)*z^2-(12976/3)*z^3-11516*z^4 := by
    dsimp [alignedPoly,P,Q,z]
    rw [dh,th]
    field_simp [show 1+y^2≠0 by positivity]
    ring
  have cubic := mul_nonneg (sq_nonneg z) (show 0≤1/3-z by linarith only [zh])
  have zsquare : 0≤1/9-z^2 := by
    have product := mul_nonneg (show 0≤1/3-z by linarith only [zh])
      (show 0≤1/3+z by linarith only [zn])
    nlinarith only [product]
  have quartic := mul_nonneg (sq_nonneg z) zsquare
  have positive : 0<400/81-(3760/27)*z+(14188/3)*z^2 := by
    have sos : 400/81-(3760/27)*z+(14188/3)*z^2=
        (14188/3)*(z-470/31923)^2+3372800/861921 := by ring
    rw [sos]
    positivity
  have weighted : 0<12500*(1+y^2)^2*alignedPoly (4/5) (3/5) d t := by
    nlinarith only [identity,cubic,quartic,positive]
  exact pos_of_mul_pos_left weighted (by positivity)

private def beforePoly (c s d t : ℝ) : ℝ :=
  c*(1-t^2-(3/50)*d*t-d)+s*((1/2)*d*t-(3/50)*t^2-t-1/2)

private theorem before_form {c s d t : ℝ} (en : Normal d t)
    (order : deltaE d t c s≤0) : FE d t c s=beforePoly c s d t := by
  by_cases branch : 0≤deltaE d t c s
  · have zero : deltaE d t c s=0 := le_antisymm order branch
    rw [FE,if_pos branch]
    dsimp [kE,E0,beforePoly,deltaE] at zero ⊢
    linear_combination (c-s/2)*en.2.2+(-d/2-(2/5)*t)*zero
  · rw [FE,if_neg branch]
    dsimp [kE,E0,beforePoly,deltaE]
    linear_combination (c-s/2)*en.2.2

private theorem before_order {c s d t d₀ t₀ : ℝ}
    (cn : Normal c s) (en : Normal d t) (base : Normal d₀ t₀)
    (order : t₀≤t) : beforePoly c s d t≤beforePoly c s d₀ t₀ := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have bb := normal_bounds base
  let D := d+d₀
  let T := t+t₀
  let J := c*T*(1-D)-(3/100)*c*(D^2-T^2)+
    s*((1/4)*(D^2-T^2)-(3/50)*D*T-D)
  have Dlo : 7/5≤D := by dsimp [D]; linarith only [eb.1,bb.1]
  have Dhi : D≤2 := by dsimp [D]; linarith only [eb.2.1,bb.2.1]
  have Tn : 0≤T := add_nonneg en.1 base.1
  have TD : T≤D := by dsimp [T,D]; linarith only [en.2.1,base.2.1]
  have square : 0≤D^2-T^2 := by
    have product := mul_nonneg (sub_nonneg.mpr TD) (by linarith only [Dlo,Tn] : 0≤D+T)
    nlinarith only [product]
  have first := mul_nonneg (mul_nonneg (show 0≤c by linarith only [cb.1]) Tn)
    (show 0≤D-1 by linarith only [Dlo])
  have second := mul_nonneg (show 0≤c by linarith only [cb.1]) square
  have last := mul_nonneg (show 0≤D by linarith only [Dlo])
    (show 0≤1-D/4 by linarith only [Dhi])
  have middle := mul_nonneg (show 0≤D by linarith only [Dlo]) Tn
  have inner : (1/4)*(D^2-T^2)-(3/50)*D*T-D≤0 := by
    nlinarith only [last,middle,sq_nonneg T]
  have third := mul_nonpos_of_nonneg_of_nonpos cn.1 inner
  have Jle : J≤0 := by dsimp [J]; nlinarith only [first,second,third]
  have identity : D*(beforePoly c s d t-beforePoly c s d₀ t₀)=(t-t₀)*J := by
    dsimp [D,T,J,beforePoly]
    linear_combination (c*(1+(3/100)*(t+t₀))-(s/4)*(t+t₀))*base.2.2-
      (c*(1+(3/100)*(t+t₀))-(s/4)*(t+t₀))*en.2.2
  have product := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr order) Jle
  rw [←identity] at product
  have result := nonpos_of_mul_nonpos_right product (show 0<D by linarith only [Dlo])
  linarith only [result]

theorem FE_before_aligned_cap {h r d t : ℝ}
    (bn : Normal h r) (en : Normal d t) (order : r≤t) :
    FE d t h r≤E0 h r := by
  have bb := normal_bounds bn
  have eb := normal_bounds en
  have cross := CommonCases.UnitCircleChord.cross_order
    (show 0≤h by linarith only [bb.1]) (show 0≤d by linarith only [eb.1])
    bn.2.2 en.2.2 bn.1 en.1 order
  have form := before_form en (show deltaE d t h r≤0 by dsimp [deltaE]; nlinarith only [cross])
  have selfForm := before_form bn (show deltaE h r h r≤0 by dsimp [deltaE]; nlinarith)
  have comparison := before_order bn en bn order
  rw [←form,←selfForm] at comparison
  have support : FE h r h r=E0 h r := by
    simp only [FE,deltaE,show h*r-r*h=0 by ring,le_refl,if_true,zero_mul,sub_zero]
    dsimp [kE]
    linear_combination (E0 h r)*bn.2.2
  simpa only [support] using comparison

theorem alignedBoundary_positive {c s d t : ℝ}
    (cn : Normal c s) (en : Normal d t) (steep : 3/5≤s) :
    0<alignedBoundary c s d t := by
  by_cases order : t≤s
  · rw [aligned_form cn en order]
    by_cases low : t≤3/5
    · have base : Normal (4/5) (3/5) := by norm_num [Normal]
      have comparison := polynomial_order cn base en (by norm_num) steep
      exact lt_of_lt_of_le (low_endpoint en low) comparison
    · have ts : 3/5≤t := (lt_of_not_ge low).le
      have comparison := polynomial_order cn en en ts order
      have value := Central.diagonal_lower en ts
      have self := aligned_self en
      rw [aligned_form en en le_rfl] at self
      linarith only [comparison,value,self]
  · have order : s≤t := (lt_of_not_ge order).le
    have cb := normal_bounds cn
    have eb := normal_bounds en
    have cross := CommonCases.UnitCircleChord.cross_order
      (show 0≤c by linarith only [cb.1]) (show 0≤d by linarith only [eb.1])
      cn.2.2 en.2.2 cn.1 en.1 order
    have form := before_form en (show deltaE d t c s≤0 by dsimp [deltaE]; nlinarith only [cross])
    have selfForm := before_form cn (show deltaE c s c s≤0 by dsimp [deltaE]; nlinarith)
    have comparison := before_order cn en cn order
    rw [←form,←selfForm] at comparison
    have product := mul_le_mul_of_nonneg_left comparison cn.1
    have self := aligned_self cn
    have value := Central.diagonal_lower cn steep
    dsimp [alignedBoundary] at self ⊢
    linarith only [product,self,value]

end
end N12Compact.C1092MPPMCrosspointSupport
