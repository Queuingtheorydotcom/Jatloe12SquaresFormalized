import Compact.Completion.OtherCases.C976LeftTop.Polynomials
import Compact.Completion.C1092.WallProfileScalars

/-! C976-LEFT-TOP-ANGLE.md sections 6--7. The original width inequality
supplies the full left half-angle interval. The sign of the actual relative
coefficient supplies the appropriate whole right interval. Exact substitution
then reduces the two support residuals to the printed bivariate quartics.
Source translation only; compiler acceptance is deferred. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.Scalars
open C1092WallProfileScalars
set_option Elab.async false

def alpha (l h C S : ℝ) : ℝ := l*C+h*S
def beta (l h C S : ℝ) : ℝ := l*S-h*C
def a0 (l h : ℝ) : ℝ := (13/100)*l+(6/25)*h
def b0 (l h : ℝ) : ℝ := (6/25)*l-(13/100)*h
def k0 (C S : ℝ) : ℝ := (13/100)*S-(6/25)*C

def Elo (l h C S : ℝ) : ℝ :=
  S*((alpha l h C S+beta l h C S)*a0 l h-(39/625)*alpha l h C S+
    k0 C S*(-(27/100)*h-(1/25)*l))+
    a0 l h*(C^2-(63/50)*C*S+C+S-2)

def Ehi (l h C S : ℝ) : ℝ :=
  S*((alpha l h C S+beta l h C S)*a0 l h-(39/625)*alpha l h C S+
    k0 C S*(l-1))+a0 l h*(C^2-(63/50)*C*S+C+S-2)

theorem left_domain (l h : ℝ) (lp : 0 < l) (hn : 0 ≤ h)
    (unit : l^2+h^2=1) (leftLow : (1/3)*l ≤ h)
    (width : 1 < (26/25)*l+(27/100)*h) :
    4/25 ≤ half l h ∧ half l h ≤ 53/163 := by
  have data := quarter_data l h lp.le hn unit
  let r := half l h
  have rn : 0 ≤ r := data.1
  have cosine : (1+r^2)*l=1-r^2 := data.2.2.2.1
  have sine : (1+r^2)*h=2*r := data.2.2.2.2
  have lowerWeighted := mul_nonneg (show 0 ≤ 1+r^2 by positivity)
    (show 0 ≤ 3*h-l by linarith only [leftLow])
  have lower : 4/25 ≤ r := by
    apply le_of_not_gt
    intro small
    have square := mul_nonneg (show 0 ≤ 4/25-r by linarith only [small])
      (show 0 ≤ 4/25+r by linarith only [rn])
    nlinarith only [lowerWeighted,cosine,sine,square,small]
  have upperWeighted := mul_pos (show 0 < 1+r^2 by positivity) (sub_pos.mpr width)
  have upper : r ≤ 53/163 := by
    apply le_of_not_gt
    intro large
    have endpoint := mul_nonneg (show 0 ≤ r-53/163 by linarith only [large])
      (show 0 ≤ 102*(r+53/163)-27 by linarith only [large])
    nlinarith only [upperWeighted,cosine,sine,endpoint]
  exact ⟨lower,upper⟩

private theorem right_domain (C S : ℝ) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (slope : C ≤ (2/3)*S) :
    0 ≤ half S C ∧ half S C ≤ 10/33 := by
  have reverseUnit : S^2+C^2=1 := by linarith only [unit]
  have data := quarter_data S C sp.le cn reverseUnit
  let w := half S C
  have wn : 0 ≤ w := data.1
  have cosine : (1+w^2)*S=1-w^2 := data.2.2.2.1
  have sine : (1+w^2)*C=2*w := data.2.2.2.2
  have weighted := mul_nonneg (show 0 ≤ 1+w^2 by positivity)
    (show 0 ≤ 2*S-3*C by linarith only [slope])
  have upper : w ≤ 10/33 := by
    apply le_of_not_gt
    intro large
    have endpoint := mul_pos (show 0 < w-10/33 by linarith only [large])
      (show 0 < w+10/33+3 by linarith only [wn])
    nlinarith only [weighted,cosine,sine,endpoint]
  exact ⟨wn,upper⟩

theorem low_domain (C S : ℝ) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (sign : 0 ≤ k0 C S) : half S C ≤ 13/50 := by
  have reverseUnit : S^2+C^2=1 := by linarith only [unit]
  have data := quarter_data S C sp.le cn reverseUnit
  let w := half S C
  have cosine : (1+w^2)*S=1-w^2 := data.2.2.2.1
  have sine : (1+w^2)*C=2*w := data.2.2.2.2
  have weighted := mul_nonneg (show 0 ≤ 1+w^2 by positivity) sign
  dsimp only [k0] at weighted
  apply le_of_not_gt
  intro large
  have square := mul_nonneg (show 0 ≤ w-13/50 by linarith only [large])
    (show 0 ≤ w+13/50 by linarith only [data.1])
  nlinarith only [weighted,cosine,sine,square,large]

theorem high_domain (C S : ℝ) (cn : 0 ≤ C) (sp : 0 < S)
    (unit : C^2+S^2=1) (sign : k0 C S ≤ 0) : 1/4 ≤ half S C := by
  have reverseUnit : S^2+C^2=1 := by linarith only [unit]
  have data := quarter_data S C sp.le cn reverseUnit
  let w := half S C
  have cosine : (1+w^2)*S=1-w^2 := data.2.2.2.1
  have sine : (1+w^2)*C=2*w := data.2.2.2.2
  have weighted := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+w^2 by positivity) sign
  dsimp only [k0] at weighted
  apply le_of_not_gt
  intro small
  have square := mul_nonneg (show 0 ≤ 1/4-w by linarith only [small])
    (show 0 ≤ 1/4+w by linarith only [data.1])
  nlinarith only [weighted,cosine,sine,square,small]

private theorem fraction_forms (c s t : ℝ)
    (cosine : (1+t^2)*c=1-t^2) (sine : (1+t^2)*s=2*t) :
    c=(1-t^2)/(1+t^2) ∧ s=(2*t)/(1+t^2) := by
  have den : 1+t^2 ≠ 0 := ne_of_gt (by positivity)
  exact ⟨(eq_div_iff den).mpr (by linarith only [cosine]),
    (eq_div_iff den).mpr (by linarith only [sine])⟩

theorem lo_identity (l h C S r w : ℝ)
    (lc : (1+r^2)*l=1-r^2) (hs : (1+r^2)*h=2*r)
    (Cs : (1+w^2)*C=2*w) (Sc : (1+w^2)*S=1-w^2) :
    10000*(1+r^2)^2*(1+w^2)^2*Elo l h C S=Polynomials.Plo r w := by
  have left := fraction_forms l h r lc hs
  have right := fraction_forms S C w Sc Cs
  have rd : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  have wd : 1+w^2 ≠ 0 := ne_of_gt (by positivity)
  dsimp only [Elo,alpha,beta,a0,k0,Polynomials.Plo]
  rw [left.1,left.2,right.1,right.2]
  field_simp [rd,wd] <;> ring

theorem hi_identity (l h C S r w : ℝ)
    (lc : (1+r^2)*l=1-r^2) (hs : (1+r^2)*h=2*r)
    (Cs : (1+w^2)*C=2*w) (Sc : (1+w^2)*S=1-w^2) :
    10000*(1+r^2)^2*(1+w^2)^2*Ehi l h C S=Polynomials.Phi r w := by
  have left := fraction_forms l h r lc hs
  have right := fraction_forms S C w Sc Cs
  have rd : 1+r^2 ≠ 0 := ne_of_gt (by positivity)
  have wd : 1+w^2 ≠ 0 := ne_of_gt (by positivity)
  dsimp only [Ehi,alpha,beta,a0,k0,Polynomials.Phi]
  rw [left.1,left.2,right.1,right.2]
  field_simp [rd,wd] <;> ring

theorem lo_positive (l h C S : ℝ) (lp : 0 < l) (hn : 0 ≤ h)
    (unit : l^2+h^2=1) (leftLow : (1/3)*l ≤ h) (leftHigh : h < (8/11)*l)
    (width : 1 < (26/25)*l+(27/100)*h)
    (cn : 0 ≤ C) (sp : 0 < S) (wallUnit : C^2+S^2=1)
    (rightSlope : C ≤ (2/3)*S) (sign : 0 ≤ k0 C S) : 0 < Elo l h C S := by
  have rRange := left_domain l h lp hn unit leftLow width
  have wRange := right_domain C S cn sp wallUnit rightSlope
  have wHigh := low_domain C S cn sp wallUnit sign
  have polynomial := Polynomials.lo_positive (half l h) (half S C)
    rRange.1 rRange.2 wRange.1 wHigh
  have left := quarter_data l h lp.le hn unit
  have reverseUnit : S^2+C^2=1 := by linarith only [wallUnit]
  have right := quarter_data S C sp.le cn reverseUnit
  have identity := lo_identity l h C S (half l h) (half S C)
    left.2.2.2.1 left.2.2.2.2 right.2.2.2.2 right.2.2.2.1
  have factor : 0 < 10000*(1+(half l h)^2)^2*(1+(half S C)^2)^2 := by positivity
  exact (mul_pos_iff_of_pos_left factor).mp (by rw [identity]; exact polynomial)

theorem hi_positive (l h C S : ℝ) (lp : 0 < l) (hn : 0 ≤ h)
    (unit : l^2+h^2=1) (leftLow : (1/3)*l ≤ h) (leftHigh : h < (8/11)*l)
    (width : 1 < (26/25)*l+(27/100)*h)
    (cn : 0 ≤ C) (sp : 0 < S) (wallUnit : C^2+S^2=1)
    (rightSlope : C ≤ (2/3)*S) (sign : k0 C S ≤ 0) : 0 < Ehi l h C S := by
  have rRange := left_domain l h lp hn unit leftLow width
  have wRange := right_domain C S cn sp wallUnit rightSlope
  have wLow := high_domain C S cn sp wallUnit sign
  have polynomial := Polynomials.hi_positive (half l h) (half S C)
    rRange.1 rRange.2 wLow wRange.2
  have left := quarter_data l h lp.le hn unit
  have reverseUnit : S^2+C^2=1 := by linarith only [wallUnit]
  have right := quarter_data S C sp.le cn reverseUnit
  have identity := hi_identity l h C S (half l h) (half S C)
    left.2.2.2.1 left.2.2.2.2 right.2.2.2.2 right.2.2.2.1
  have factor : 0 < 10000*(1+(half l h)^2)^2*(1+(half S C)^2)^2 := by positivity
  exact (mul_pos_iff_of_pos_left factor).mp (by rw [identity]; exact polynomial)

end N12Compact.Completion.OtherCases.C976LeftTop.Scalars
