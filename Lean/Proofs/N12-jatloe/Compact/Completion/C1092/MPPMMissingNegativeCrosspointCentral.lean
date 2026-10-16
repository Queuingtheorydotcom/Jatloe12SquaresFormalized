import Compact.Completion.C1092.MPPMMissingNegativeCrosspointScalars
import Compact.Completion.C1092.MPPMNegativeCrosspointCentral

/-! MISSING-NEGATIVE-WALL-SCALARS section 3. The same three exact
circle chords give the full width bound. Rational .71 coordinate caps
replace the manuscript's sqrt(2) estimate and leave the uniform positive
margin 1/250 after the complete epsilon allowance. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C977CornerCubic
set_option Elab.async false
noncomputable section

theorem width_lower {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (large : 252/373≤t) (q : Quarter h r) :
    (14/5)*ell c s d t≤width c s d t h r := by
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cs := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have es := C1092MPPMCrosspointSupport.steep_bounds en
    (show 3/5≤t by linarith only [large])
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := C977CornerSectorBounds.cosine_order en endpoint large
  have cp : 0≤c := by linarith only [cb.1]
  have dp : 0≤d := by linarith only [eb.1]
  have tn : 0≤t := en.1
  have enon : 0≤ell c s d t :=
    add_nonneg (mul_nonneg cp en.1) (mul_nonneg cn.1 dp)
  have first := mul_nonneg en.1 (show 0≤4*s-3*c by linarith only [cs.1,steep])
  have last := mul_nonneg cn.1 (show 0≤11*t-10*d by linarith only [cosine,large])
  have st : 0≤s*t := mul_nonneg cn.1 en.1
  have coordinate : 0≤2*ell c s d t+2*s*t-(14/5)*ell c s d t := by
    dsimp [ell,C1092MPPMNegativeCrosspointSupport.ell]
    nlinarith only [first,last,st]
  have left := mul_nonneg enon (show 0≤c+s-7/5 by linarith only [cs.2.2.1])
  have right := mul_nonneg enon (show 0≤d+t-7/5 by linarith only [es.2.2.1])
  have upper : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
  have eq : t^2+d^2=1 := by nlinarith only [en.2.2]
  by_cases low : r≤s
  · have f0 : 0≤-(14/5)*ell c s d t+(2*ell c s d t+2*s*t)*1+(2*s*d)*0 := by
      nlinarith only [coordinate]
    have f1 : 0≤-(14/5)*ell c s d t+(2*ell c s d t+2*s*t)*c+(2*s*d)*s := by
      dsimp [ell,C1092MPPMNegativeCrosspointSupport.ell] at left ⊢
      nlinarith only [left]
    have chord := CommonCases.UnitCircleChord.linear_nonnegative
      (by norm_num : (0:ℝ)≤1) cp q.cosine (by norm_num : (1:ℝ)^2+0^2=1)
      cn.2.2 q.unit q.sine low (by linarith only [enon,st]) f0 f1
    have below := C1092MPPMNegativeCrosspointSupport.low_below (h:=h) (r:=r) cn en
    linarith only [chord,below]
  · have low : s≤r := (lt_of_not_ge low).le
    by_cases high : r≤d
    · have f0 : 0≤-(14/5)*ell c s d t+(2*ell c s d t)*c+(2*ell c s d t)*s := by
        nlinarith only [left]
      have f1 : 0≤-(14/5)*ell c s d t+(2*ell c s d t)*t+(2*ell c s d t)*d := by
        nlinarith only [right]
      have chord := CommonCases.UnitCircleChord.linear_nonnegative cp en.1 q.cosine
        cn.2.2 eq q.unit low high (by linarith only [enon]) f0 f1
      have below := C1092MPPMNegativeCrosspointSupport.middle_below (h:=h) (r:=r) cn en
      linarith only [chord,below]
    · have f0 : 0≤-(14/5)*ell c s d t+(2*c*t)*t+(2*ell c s d t+2*s*t)*d := by
        dsimp [ell,C1092MPPMNegativeCrosspointSupport.ell] at right ⊢
        nlinarith only [right]
      have f1 : 0≤-(14/5)*ell c s d t+(2*c*t)*0+(2*ell c s d t+2*s*t)*1 := by
        nlinarith only [coordinate]
      have chord := CommonCases.UnitCircleChord.linear_nonnegative en.1
        (by norm_num : (0:ℝ)≤0) q.cosine eq (by norm_num : (0:ℝ)^2+1^2=1)
        q.unit (lt_of_not_ge high).le upper (by positivity : 0≤2*c*t) f0 f1
      have below := C1092MPPMNegativeCrosspointSupport.high_below (h:=h) (r:=r) cn en
      linarith only [chord,below]

theorem G00_lower {c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (large : 252/373≤t) (q : Quarter h r) :
    47/1000≤G00 c s d t h r := by
  have wb := width_lower cn en steep large q
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have cs := C1092MPPMCrosspointSupport.steep_bounds cn steep
  have es := C1092MPPMCrosspointSupport.steep_bounds en
    (show 3/5≤t by linarith only [large])
  have positive := mul_nonneg (show 0≤71/100-s by linarith only [cs.2.1])
    (show 0≤t-1/2 by linarith only [large])
  have minimum : 2059/5000≤s+t-2*s*t := by nlinarith only [positive,es.2.1]
  have sd := mul_nonneg (show 0≤s-3/5 by exact sub_nonneg.mpr steep)
    (show 0≤d by linarith only [eb.1])
  have sdLower : 21/50≤s*d := by nlinarith only [sd,eb.1]
  have ellUpper : ell c s d t≤1 := by
    dsimp [ell,C1092MPPMNegativeCrosspointSupport.ell]
    nlinarith only [cn.2.2,en.2.2,sq_nonneg (c-t),sq_nonneg (s-d)]
  dsimp [G00,C0,E0,C1092MPPMNegativeCrosspointSupport.C0] at *
  nlinarith only [wb,minimum,sdLower,ellUpper]

theorem G00star_lower {epsilon c s d t h r : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (large : 252/373≤t) (q : Quarter h r)
    (allowance : epsilon≤43/500) : 1/250≤G00star epsilon c s d t h r := by
  have base := G00_lower cn en steep large q
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have squareC := mul_nonneg (sub_nonneg.mpr cn.2.1) (show 0≤c+s by linarith only [cb.1,cn.1])
  have squareE := mul_nonneg (sub_nonneg.mpr en.2.1) (show 0≤d+t by linarith only [eb.1,en.1])
  have stUpper : s*t≤1/2 := by nlinarith only [squareC,squareE,cn.2.2,en.2.2,sq_nonneg (s-t)]
  have perturb := mul_le_mul_of_nonneg_right allowance (mul_nonneg cn.1 en.1)
  have perturbUpper : epsilon*s*t≤43/1000 := by nlinarith only [perturb,stUpper]
  dsimp [G00star]
  linarith only [base,perturbUpper]

end
#print axioms G00star_lower
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
