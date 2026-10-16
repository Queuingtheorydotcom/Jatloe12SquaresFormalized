import Compact.Completion.C1092.MPPMMissingNegativeCrosspointEnvelope
import Compact.Completion.C1092.MPPMNegativeCrosspointG01Quartic

/-! MISSING-NEGATIVE-WALL-SCALARS §4. Two rational quartics replace
the two derivative arguments. They retain a uniform .06 reserve; the
actual-side allowance is handled only in the final scalar theorem. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport.G10Scalars
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem quarter_bounds {h r : ℝ} (q : Quarter h r) :
    h≤1 ∧ r≤1 ∧ 1≤h+r ∧ h+r≤10/7 := by
  have hh : h≤1 := by nlinarith only [q.unit,sq_nonneg r,sq_nonneg (h-1)]
  have rr : r≤1 := by nlinarith only [q.unit,sq_nonneg h,sq_nonneg (r-1)]
  have hsq := mul_nonneg q.cosine (sub_nonneg.mpr hh)
  have rsq := mul_nonneg q.sine (sub_nonneg.mpr rr)
  exact ⟨hh,rr,by nlinarith only [hsq,rsq,q.unit],
    by nlinarith only [q.unit,sq_nonneg (h-r),sq_nonneg (h+r-10/7)]⟩

theorem recipient_bounds {d t : ℝ} (en : Normal d t) (large : 252/373≤t) :
    d≤3/4 ∧ 27/40≤t ∧ t≤3/4 := by
  have endpoint : Normal (275/373:ℝ) (252/373) := by norm_num [Normal]
  have cosine := C977CornerSectorBounds.cosine_order en endpoint large
  have sine := C1092MPPMCrosspointSupport.steep_bounds en
    (show 3/5≤t by linarith only [large])
  exact ⟨by linarith only [cosine],by linarith only [large],by linarith only [sine.2.1]⟩

theorem before_formula (c s d t h r : ℝ) (q : Quarter h r)
    (branch : deltaE d t h r≤0) :
    G10 c s d t h r=t*(h*(h+r)-2*h-r-FC c s h r)+d*r*(h+r-36/25)+r := by
  unfold G10
  rw [abs_of_nonpos branch]
  dsimp [kE,deltaE,E0,C1092MPPMNegativeCrosspointSupport.kE,
    C1092MPPMNegativeCrosspointSupport.deltaE]
  linear_combination -(t/2)*q.unit

theorem after_formula (c s d t h r : ℝ) (q : Quarter h r)
    (branch : 0≤deltaE d t h r) :
    G10 c s d t h r=t*(1+h*r-2*h-r-FC c s h r)+d*r*(r-36/25)+r := by
  unfold G10
  rw [abs_of_nonneg branch]
  dsimp [kE,deltaE,E0,C1092MPPMNegativeCrosspointSupport.kE,
    C1092MPPMNegativeCrosspointSupport.deltaE]
  linear_combination (t/2)*q.unit

theorem low_bounds {h r : ℝ} (q : Quarter h r) (low : r≤3/5) :
    4/5≤h ∧ r≤h ∧ h+r≤7/5 := by
  have fixed : Normal (4/5:ℝ) (3/5) := by norm_num [Normal]
  have cosine := CommonCases.UnitCircleChord.cosine_order q.cosine
    (by norm_num : (0:ℝ)≤4/5) q.unit fixed.2.2 q.sine fixed.1 low
  have sum := CommonCases.UnitCircleChord.increasing (A:=(1:ℝ)) (B:=1)
    (by norm_num : (0:ℝ)<4/5) q.cosine fixed.2.2 q.unit fixed.1 q.sine low
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨cosine,by linarith only [cosine,low],by linarith only [sum]⟩

theorem low_radial {h r : ℝ} (q : Quarter h r) (low : r≤3/5) :
    9/125≤3/4-(63/100)*h-(149/100)*r+(3/2)*h*r := by
  have hb := low_bounds q low
  let z := half h r
  have data := quarter_data h r q.cosine q.sine q.unit
  have zn : 0≤z := data.1
  have zu : z≤1/3 := by
    change r/(1+h)≤1/3
    apply (div_le_iff₀ (show 0<1+h by linarith only [q.cosine])).mpr
    linarith only [low,hb.1]
  have Dp : 0<1+z^2 := by positivity
  have hform : h=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.1]
  have rform : r=2*z/(1+z^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.2]
  have poly := C1092MPPMNegativeCrosspointSupport.G01Quartic.bernstein
    (6/125) (1/50) (339/250) (-299/50) (327/250) (1/3) z
    (by norm_num) zn zu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly])
  have identity : (1+z^2)^2*(3/4-(63/100)*h-(149/100)*r+(3/2)*h*r-9/125)=
      C1092MPPMNegativeCrosspointSupport.G01Quartic.poly
        (6/125) (1/50) (339/250) (-299/50) (327/250) z := by
    rw [hform,rform]
    dsimp [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly]
    field_simp [Dp.ne'] <;> ring
  rw [←identity] at poly
  have nonnegative := nonneg_of_mul_nonneg_right poly (sq_pos_of_pos Dp)
  linarith only [nonnegative]

theorem high_radial {h r : ℝ} (q : Quarter h r) (order : h≤r) :
    3/50≤3/4+(3/4)*h*r-(9/8)*h+(3/4)*r^2-(359/400)*r := by
  let z := half r h
  have data := quarter_data r h q.sine q.cosine (by nlinarith only [q.unit])
  have zn : 0≤z := data.1
  have zu : z≤5/12 := C1092MPPMNegativeCrosspointSupport.G01Quartic.parameter_bound q order
  have Dp : 0<1+z^2 := by positivity
  have hform : h=2*z/(1+z^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.2]
  have rform : r=(1-z^2)/(1+z^2) := by
    apply (eq_div_iff Dp.ne').mpr
    nlinarith only [data.2.2.2.1]
  have poly := C1092MPPMNegativeCrosspointSupport.G01Quartic.bernstein
    (217/400) (-3/4) (-3/25) (-15/4) (187/80) (5/12) z
    (by norm_num) zn zu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly])
  have identity : (1+z^2)^2*(3/4+(3/4)*h*r-(9/8)*h+(3/4)*r^2-(359/400)*r-3/50)=
      C1092MPPMNegativeCrosspointSupport.G01Quartic.poly
        (217/400) (-3/4) (-3/25) (-15/4) (187/80) z := by
    rw [hform,rform]
    dsimp [C1092MPPMNegativeCrosspointSupport.G01Quartic.poly]
    field_simp [Dp.ne'] <;> ring
  rw [←identity] at poly
  have nonnegative := nonneg_of_mul_nonneg_right poly (sq_pos_of_pos Dp)
  linarith only [nonnegative]

#print axioms before_formula
#print axioms after_formula
end
end N12Compact.C1092MPPMMissingNegativeCrosspointSupport.G10Scalars
