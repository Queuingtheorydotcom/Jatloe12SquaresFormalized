import Compact.Completion.C1092.TwoFifthsData
import Compact.Completion.C1092.MMMP.PositiveInwardHalfangle

/-! Exact southeast scalar estimates. The key slope quotient and both
loss comparisons use polynomial differences on the whole interval.
This replaces the manuscript derivatives without angle sampling. -/
namespace N12Compact.C1092TwoFifths.Scalars
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

structure SouthBounds (c s z : ℝ) : Prop where
  cosine : 47/50<c
  cosineUpper : c≤1
  sine : 0<s
  sineUpper : s<8/25
  halfPositive : 0<z
  halfUpper : z<1/6
  relation : z*(1+c)=s
  circle : s*z=1-c
  eta : z*(1-s)<113/1000
  key : 5*z*(c+s)<2*((13/50)+s*(1-z))

theorem south_bounds (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (small : 3*s<c) (unit : c^2+s^2=1) : SouthBounds c s (half c s) := by
  have cone := mul_pos (show 0<c-3*s by linarith only [small])
    (show 0<c+3*s by linarith only [cp,sp])
  have cosine : 47/50<c := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤47/50-c by linarith only [bad])
      (show 0≤47/50+c by linarith only [cp])
    nlinarith only [cone,unit,product]
  have cu : c≤1 := by nlinarith only [unit,sq_nonneg s,sq_nonneg (c-1)]
  have sine : s<8/25 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤s-8/25 by linarith only [bad])
      (show 0≤s+8/25 by linarith only [sp])
    nlinarith only [cone,unit,product]
  have den : 0<1+c := by linarith only [cp]
  have zp : 0<half c s := div_pos sp den
  have identities := C1092MMMPPositiveInwardHalfangle.half_identities c s cp unit
  have zu : half c s<1/6 := by
    dsimp [half]
    apply (div_lt_iff₀ den).mpr
    linarith only [cosine,sine]
  have eta : half c s*(1-s)<113/1000 := by
    have cap := mul_nonneg (show 0≤8/25-s by linarith only [sine])
      (show 0≤1-8/25-s by linarith only [sine])
    have identity : (1+c)*(half c s*(1-s))=s*(1-s) := by
      linear_combination (1-s)*identities.1
    have gap : 0<(1+c)*(113/1000-half c s*(1-s)) := by
      nlinarith only [identity,cap,cosine]
    exact sub_pos.mp (pos_of_mul_pos_right gap den.le)
  have tangent : c≤1-s^2/2 := by nlinarith only [unit,sq_nonneg (c-1)]
  have weighted := mul_le_mul_of_nonneg_left tangent (show 0≤3*s by linarith only [sp])
  have square : s^2≤(8/25)^2 := by
    have bound := mul_nonneg (show 0≤8/25-s by linarith only [sine])
      (show 0≤8/25+s by linarith only [sp])
    nlinarith only [bound]
  have coefficient : 0≤1+7*(s+8/25)-(3/2)*(s^2+(8/25)*s+(8/25)^2) := by
    nlinarith only [square,sp]
  have difference := mul_nonneg (show 0≤8/25-s by linarith only [sine]) coefficient
  have positive : 0<(13/25)*(1+c)+2*s-3*c*s-7*s^2 := by
    nlinarith only [difference,weighted,cosine]
  have identity : (1+c)*(2*((13/50)+s*(1-half c s))-5*half c s*(c+s))=
      (13/25)*(1+c)+2*s-3*c*s-7*s^2 := by
    linear_combination -(5*c+7*s)*identities.1
  have key : 5*half c s*(c+s)<2*((13/50)+s*(1-half c s)) := by
    have gap : 0<(1+c)*(2*((13/50)+s*(1-half c s))-5*half c s*(c+s)) := by
      rw [identity]
      exact positive
    exact sub_pos.mp (pos_of_mul_pos_right gap den.le)
  exact ⟨cosine,cu,sp,sine,zp,zu,identities.1,identities.2,eta,key⟩

/-- One factored product gives the exact threshold 10/29 for d*r. -/
theorem right_large (d r : ℝ) (normal : Normal d r) (large : (2/5)*d≤r) :
    10/29≤d*r ∧ 4/29≤r^2 ∧ r^2≤1/2 := by
  have b := normal_bounds normal
  have product := mul_nonneg (show 0≤5*r-2*d by linarith only [large])
    (show 0≤5*d-2*r by linarith only [normal.1,normal.2.1])
  have squares := mul_nonneg (show 0≤5*r-2*d by linarith only [large])
    (show 0≤5*r+2*d by linarith only [normal.1,b.1])
  have ordered := mul_nonneg (sub_nonneg.mpr normal.2.1)
    (show 0≤d+r by linarith only [normal.1,b.1])
  exact ⟨by nlinarith only [product,normal.2.2],
    by nlinarith only [squares,normal.2.2],
    by nlinarith only [ordered,normal.2.2]⟩

theorem negative_loss (c s z d r : ℝ) (h : SouthBounds c s z)
    (normal : Normal d r) (large : (2/5)*d≤r) :
    113/1000<(33/50)*c*d*r+s*((13/50)*d^2-(2/5)*r^2) := by
  have b := right_large d r normal large
  have first := mul_pos (sub_pos.mpr h.cosine) (show 0<d*r by linarith only [b.1])
  have lower : -(7/100)≤(13/50)*d^2-(2/5)*r^2 := by
    nlinarith only [normal.2.2,b.2.2]
  have last := mul_le_mul_of_nonneg_left lower h.sine.le
  nlinarith only [first,b.1,last,h.sineUpper]

theorem positive_loss (c s z d r : ℝ) (h : SouthBounds c s z)
    (normal : Normal d r) (large : (2/5)*d≤r) :
    113/1000<(33/50)*c*d*r-s*((2/5)*d^2-(13/50)*r^2) := by
  have b := right_large d r normal large
  have first := mul_pos (sub_pos.mpr h.cosine) (show 0<d*r by linarith only [b.1])
  have cap : (2/5)*d^2-(13/50)*r^2≤224/725 := by
    nlinarith only [normal.2.2,b.2.1]
  have last := mul_le_mul_of_nonneg_left cap h.sine.le
  nlinarith only [first,b.1,last,h.sineUpper]

end
#print axioms south_bounds
#print axioms negative_loss
#print axioms positive_loss
end N12Compact.C1092TwoFifths.Scalars
