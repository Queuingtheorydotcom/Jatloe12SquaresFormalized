import Compact.Completion.C981.HalfAngle
import Compact.Completion.CommonCases.CanonicalProjection

namespace N12Compact.CommonCases.C702NorthScalars
set_option Elab.async false

theorem shallow_margin (c s : ℝ) (cp : 0 < c) (sp : 0 < s)
    (order : s ≤ c) (unit : c^2+s^2=1) (shallow : 13*s ≤ 9*c) :
    1 < c+(3/20)*c*s+(7/20)*s^2 := by
  have data := C981CompletionHalfAngle.data c s cp.le sp.le order unit
  let t := C981CompletionHalfAngle.half c s
  have tn : 0 ≤ t := data.1
  have tp : 0 < t := div_pos sp (by linarith only [cp])
  have cform : (1+t^2)*c=1-t^2 := data.2.2.2.1
  have sform : (1+t^2)*s=2*t := data.2.2.2.2
  have weighted := mul_nonneg (show 0 ≤ 1+t^2 by positivity)
    (show 0 ≤ 9*c-13*s by linarith only [shallow])
  have quadratic : 9*t^2+26*t ≤ 9 := by linarith only [weighted,cform,sform]
  have tu : t < 8/25 := by
    by_contra bad
    have low : 8/25 ≤ t := by exact le_of_not_gt bad
    have square := mul_nonneg (show 0 ≤ t-8/25 by linarith only [low])
      (show 0 ≤ t+8/25 by linarith only [tn])
    nlinarith only [quadratic,low,square]
  have square := mul_nonneg (show 0 ≤ 8/25-t by linarith only [tu])
    (show 0 ≤ 8/25+t by linarith only [tn])
  have cubic := mul_nonneg (show 0 ≤ 8/25-t by linarith only [tu])
    (show 0 ≤ (8/25)^2+(8/25)*t+t^2 by positivity)
  have polynomial : 0 < 3-6*t-3*t^2-20*t^3 := by
    nlinarith only [square,cubic,tu]
  have identity :
      (c+(3/20)*c*s+(7/20)*s^2-1)*(10*(1+t^2)^2) =
        t*(3-6*t-3*t^2-20*t^3) := by
    calc
      _ = 10*((1+t^2)*c)*(1+t^2)+(3/2)*((1+t^2)*c)*((1+t^2)*s)+
          (7/2)*((1+t^2)*s)^2-10*(1+t^2)^2 := by ring
      _ = _ := by rw [cform,sform]; ring
  have numerator := mul_pos tp polynomial
  have margin : 0 < c+(3/20)*c*s+(7/20)*s^2-1 :=
    pos_of_mul_pos_left (by rwa [←identity] at numerator) (by positivity)
  linarith only [margin]

theorem steep_bounds (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) (steep : 9*c < 13*s) : c < 5/6 ∧ 14/25 < s := by
  have product := mul_pos (show 0 < 13*s-9*c by linarith only [steep])
    (show 0 < 13*s+9*c by linarith only [cp,sn])
  constructor
  · by_contra bad
    have high : 5/6 ≤ c := by exact le_of_not_gt bad
    have square := mul_nonneg (show 0 ≤ c-5/6 by linarith only [high])
      (show 0 ≤ c+5/6 by linarith only [cp])
    nlinarith only [unit,product,square]
  · by_contra bad
    have low : s ≤ 14/25 := by exact le_of_not_gt bad
    have square := mul_nonneg (show 0 ≤ 14/25-s by linarith only [low])
      (show 0 ≤ 14/25+s by linarith only [sn])
    nlinarith only [unit,product,square]

theorem negative_gap (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) (steep : 5*c < 6*s) : (63/50)*c < 1 := by
  have product := mul_pos (show 0 < 6*s-5*c by linarith only [steep])
    (show 0 < 6*s+5*c by linarith only [cp,sn])
  by_contra bad
  have high : 50/63 ≤ c := by linarith only [le_of_not_gt bad]
  have square := mul_nonneg (show 0 ≤ c-50/63 by linarith only [high])
    (show 0 ≤ c+50/63 by linarith only [cp])
  nlinarith only [unit,product,square]

end N12Compact.CommonCases.C702NorthScalars
