import Compact.Completion.OtherCases.SouthwestSupportPoint.Polynomials
import Compact.Completion.C1092.WallProfileScalars

/-! The five whole-interval scalar comparisons in
C974-C976-SW-SUPPORT-POINT.md sections 4--7. A single quadratic substitution
identity connects the physical support expressions to the exact quartics.
All angle endpoints in the chapter are retained. Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint.Scalars
open C1092WallProfileScalars
set_option Elab.async false

def f1 (c s : ℝ) : ℝ :=
  (35*c+9*s)+(9*c-35*s)-(35*c+9*s)*((73/100)*c+(1/25)*s)+
    (9*c-35*s)*((2/5)*s-c)-91/10
def f2 (c s : ℝ) : ℝ :=
  (35*c+9*s)*(1-(73/100)*c-(1/25)*s)-(13/50)*c*(9*c-35*s)-91/10
def f3 (c s : ℝ) : ℝ := c+s-24/25+(31/100)*s^2-(27/25)*c*s
def f4 (c s : ℝ) : ℝ :=
  (35*c-9*s)+(35*s+9*c)+(35*c-9*s)*(-(73/100)*c+(1/25)*s)-
    (35*s+9*c)*c-91/10
def f5 (c s : ℝ) : ℝ :=
  (35*c-9*s)+(35*s+9*c)+(35*c-9*s)*(-(73/100)*c+(1/25)*s)+
    (35*s+9*c)*(-(13/50)*s-c)-91/10

private theorem scale_quadratic (c s t A B C D E F : ℝ)
    (cosine : (1+t^2)*c=1-t^2) (sine : (1+t^2)*s=2*t) :
    (1+t^2)^2*(A+B*c+C*s+D*c^2+E*c*s+F*s^2) =
      A*(1+t^2)^2+B*(1+t^2)*(1-t^2)+C*(1+t^2)*(2*t)+
      D*(1-t^2)^2+E*(1-t^2)*(2*t)+F*(2*t)^2 := by
  calc
    _ = A*(1+t^2)^2+B*(1+t^2)*((1+t^2)*c)+C*(1+t^2)*((1+t^2)*s)+
        D*((1+t^2)*c)^2+E*((1+t^2)*c)*((1+t^2)*s)+F*((1+t^2)*s)^2 := by ring
    _ = _ := by rw [cosine,sine]

private theorem unscale (t f p : ℝ) (identity : (1+t^2)^2*f=p)
    (positive : 0 < p) : 0 < f := by
  have factor : 0 < (1+t^2)^2 := sq_pos_of_pos (by positivity)
  exact (mul_pos_iff_of_pos_left factor).mp (by rw [identity]; exact positive)

theorem f1_identity (c s t : ℝ) (cosine : (1+t^2)*c=1-t^2)
    (sine : (1+t^2)*s=2*t) : (1+t^2)^2*f1 c s=Polynomials.p1 t := by
  have identity := scale_quadratic c s t (-91/10) 44 (-26) (-691/20)
    (3063/100) (-359/25) cosine sine
  convert identity using 1 <;> dsimp only [f1,Polynomials.p1] <;> ring

theorem f2_identity (c s t : ℝ) (cosine : (1+t^2)*c=1-t^2)
    (sine : (1+t^2)*s=2*t) : (1+t^2)^2*f2 c s=Polynomials.p2 t := by
  have identity := scale_quadratic c s t (-91/10) 35 9 (-2789/100)
    (113/100) (-9/25) cosine sine
  convert identity using 1 <;> dsimp only [f2,Polynomials.p2] <;> ring

theorem f3_identity (c s t : ℝ) (cosine : (1+t^2)*c=1-t^2)
    (sine : (1+t^2)*s=2*t) : (1+t^2)^2*f3 c s=Polynomials.p3 t := by
  have identity := scale_quadratic c s t (-24/25) 1 1 0 (-27/25) (31/100) cosine sine
  convert identity using 1 <;> dsimp only [f3,Polynomials.p3] <;> ring

theorem f4_identity (c s t : ℝ) (cosine : (1+t^2)*c=1-t^2)
    (sine : (1+t^2)*s=2*t) : (1+t^2)^2*f4 c s=Polynomials.p4 t := by
  have identity := scale_quadratic c s t (-91/10) 44 26 (-691/20)
    (-2703/100) (-9/25) cosine sine
  convert identity using 1 <;> dsimp only [f4,Polynomials.p4] <;> ring

theorem f5_identity (c s t : ℝ) (cosine : (1+t^2)*c=1-t^2)
    (sine : (1+t^2)*s=2*t) : (1+t^2)^2*f5 c s=Polynomials.p5 t := by
  have identity := scale_quadratic c s t (-91/10) 44 26 (-691/20)
    (-2937/100) (-473/50) cosine sine
  convert identity using 1 <;> dsimp only [f5,Polynomials.p5] <;> ring

theorem canonical_half_upper (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) : half c s < 5/12 := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have cosine : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sine : (1+t^2)*s=2*t := data.2.2.2.2
  have weighted := mul_nonneg (show 0 ≤ 1+t^2 by positivity) (sub_nonneg.mpr order)
  apply lt_of_not_ge
  intro high
  have lower : 5/12 ≤ t := high
  have square := mul_nonneg (sub_nonneg.mpr lower)
    (show 0 ≤ t+5/12 by linarith only [data.1])
  nlinarith only [weighted,cosine,sine,square,lower]

theorem positive_low (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (sign : 0 ≤ 9*c-35*s) : 0 < f1 c s := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have cosine : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sine : (1+t^2)*s=2*t := data.2.2.2.2
  have weighted := mul_nonneg (show 0 ≤ 1+t^2 by positivity) sign
  have hi : t ≤ 1/7 := by nlinarith only [weighted,cosine,sine,sq_nonneg t]
  exact unscale t _ _ (f1_identity c s t cosine sine) (Polynomials.p1_positive t data.1 hi)

theorem positive_high (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (sign : 9*c-35*s ≤ 0) : 0 < f2 c s := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have cosine : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sine : (1+t^2)*s=2*t := data.2.2.2.2
  have weighted := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+t^2 by positivity) sign
  have lo : 1/8 ≤ t := by
    apply le_of_not_gt
    intro low
    have square := mul_nonneg (show 0 ≤ 1/8-t by linarith only [low])
      (show 0 ≤ 1/8+t by linarith only [data.1])
    nlinarith only [weighted,cosine,sine,square,low]
  have hi : t ≤ 5/12 := (canonical_half_upper c s cp sn order unit).le
  exact unscale t _ _ (f2_identity c s t cosine sine) (Polynomials.p2_positive t lo hi)

theorem positive_vertex (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (slope : s ≤ (3/4)*c) : 0 < f3 c s := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have cosine : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sine : (1+t^2)*s=2*t := data.2.2.2.2
  have weighted := mul_nonneg (show 0 ≤ 1+t^2 by positivity)
    (show 0 ≤ 3*c-4*s by linarith only [slope])
  have hi : t ≤ 1/3 := by
    apply le_of_not_gt
    intro high
    have bad := mul_pos (show 0 < t-1/3 by linarith only [high])
      (show 0 < 3*t+9 by linarith only [data.1])
    nlinarith only [weighted,cosine,sine,bad]
  exact unscale t _ _ (f3_identity c s t cosine sine) (Polynomials.p3_positive t data.1 hi)

theorem negative_lower (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) : 0 < f4 c s := by
  have data := quarter_data c s cp.le sn unit
  have hi := (canonical_half_upper c s cp sn order unit).le
  exact unscale (half c s) _ _ (f4_identity c s _ data.2.2.2.1 data.2.2.2.2)
    (Polynomials.p4_positive _ data.1 hi)

theorem half_lower_of_span (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) (span : 1 < (73/100)*c+(24/25)*s) :
    4/25 < half c s := by
  have data := quarter_data c s cp.le sn unit
  let t := half c s
  have cosine : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sine : (1+t^2)*s=2*t := data.2.2.2.2
  have weighted := mul_pos (show 0 < 1+t^2 by positivity) (sub_pos.mpr span)
  apply lt_of_not_ge
  intro low
  have endpoint := mul_nonneg (show 0 ≤ 4/25-t by linarith only [low])
    (show 0 ≤ 48/25-(173/100)*(4/25+t) by linarith only [low])
  nlinarith only [weighted,cosine,sine,endpoint]

theorem negative_upper (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s) (order : s ≤ c)
    (unit : c^2+s^2=1) (lo : 4/25 ≤ half c s) : 0 < f5 c s := by
  have data := quarter_data c s cp.le sn unit
  have hi := (canonical_half_upper c s cp sn order unit).le
  exact unscale (half c s) _ _ (f5_identity c s _ data.2.2.2.1 data.2.2.2.2)
    (Polynomials.p5_positive _ lo hi)

end N12Compact.Completion.OtherCases.SouthwestSupportPoint.Scalars
