import Compact.Geometry.C977CornerCubic

/-! Continuous margins for the complete merged-left/merged-bottom pair
in original case84. The interval below is forced by the actual missing
G5 point. It is one continuous arc, with no angle enumeration. -/
namespace N12Compact.C84PairMargins

open C977CornerCubic
set_option Elab.async false

noncomputable def A (c s : ℝ) : ℝ :=
  13/50+(13/50)*s^2-(43/500)*c*s-s

noncomputable def D (c s : ℝ) : ℝ :=
  -1-(43/500)*s^2-(13/50)*c*s+c

private theorem arc {c s : ℝ} (normal : Normal c s) :
    1+(4/5)*c*s≤c+s := by
  have bounds := normal_bounds normal
  have factor := mul_nonneg (sub_nonneg.mpr bounds.2.2.2.2.1)
    (show 0≤1-(2/5)*(c+s+1) by linarith only [bounds.2.2.2.2.2])
  nlinarith only [factor,normal.2.2]

/-- Four endpoint margins suffice for both signs of the left square.
The small rational gap in the middle margin is preserved exactly. -/
theorem margins {c s : ℝ} (normal : Normal c s) (steep : 3/10≤s) :
    A c s<0 ∧ D c s≤0 ∧ 35*A c s-9*D c s<0 ∧
      A c s-D c s-13/50<0 := by
  have bounds := normal_bounds normal
  have cp : 0<c := by linarith only [bounds.1]
  have sp : 0<s := by linarith only [steep]
  have ordered := mul_nonneg (sub_nonneg.mpr normal.2.1)
    (show 0≤c+s by linarith only [cp,normal.1])
  have square : s^2≤1/2 := by nlinarith only [ordered,normal.2.2]
  have upper : s≤71/100 := by
    nlinarith only [square,sq_nonneg (s-71/100)]
  have secant := mul_nonneg (sub_nonneg.mpr steep) (sub_nonneg.mpr upper)
  have orderProduct := mul_nonneg normal.1 (sub_nonneg.mpr normal.2.1)
  have positiveProduct := mul_pos cp sp
  have defectProduct := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0≤(3/5)*c-2/5 by linarith only [bounds.1])
  have defect : 1-c≤(3/5)*s^2 := by
    nlinarith only [defectProduct,normal.2.2]
  have arcBound := arc normal
  unfold A D
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [steep,secant,orderProduct]
  · nlinarith only [bounds.2.1,positiveProduct,sq_nonneg s]
  · nlinarith only [steep,secant,defect,positiveProduct]
  · nlinarith only [arcBound,orderProduct,positiveProduct]

theorem diagonal {c s : ℝ} (normal : Normal c s) (steep : 3/10≤s) :
    0<c+s-1-(87/500)*c*s-(173/500)*s^2 := by
  have bound := (margins normal steep).2.2.2
  dsimp [A,D] at bound
  linarith only [bound]

theorem parallel {c s : ℝ} (normal : Normal c s) :
    0<1-(13/20)*c-(61/100)*s := by
  have square : ((13/20)*c+(61/100)*s)^2≤3973/5000 := by
    nlinarith only [normal.2.2,sq_nonneg ((61/100)*c-(13/20)*s)]
  nlinarith only [square,sq_nonneg ((13/20)*c+(61/100)*s-1)]

#print axioms margins
end N12Compact.C84PairMargins
