import Compact.Completion.CommonCases.CanonicalScalars

/-! Two support margins for C702's southwest point. The negative margin
uses c+s≥7/5−(2/5)(c−s)², avoiding the paper's quartic Bernstein expansion. -/
namespace N12Compact.CommonCases.C702SouthScalars
set_option Elab.async false

theorem shallow_margin (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) (shallow : 11*s < c) :
    0 < (4/5)*c+(3/5)*s+(59/500)*s^2-(22/125)*c*s-63/100 := by
  have cu : c ≤ 1 := by nlinarith only [unit,sq_nonneg s,cp]
  have ratio := mul_nonneg (show 0 ≤ c-11*s by linarith only [shallow])
    (show 0 ≤ c+11*s by linarith only [cp,sn])
  have cLow : 11/12 < c := by
    by_contra bad
    have bound : c ≤ 11/12 := by exact le_of_not_gt bad
    have square := mul_nonneg (show 0 ≤ 11/12-c by linarith only [bound])
      (show 0 ≤ 11/12+c by linarith only [cp])
    nlinarith only [unit,ratio,square]
  have product := mul_nonneg sn
    (show 0 ≤ 3/5-(22/125)*c by linarith only [cu])
  nlinarith only [cLow,product,sq_nonneg s]

private theorem negative_margin_dv (d v : ℝ) (dn : 0≤d) (du : d≤1)
    (vlow : 1≤v) (norm : v^2+d^2=2) :
    0<(4/5-(419/1000)*d)*v+(3/5)*d+(267/1000)*d^2-539/500 := by
  have square := mul_nonneg dn (show 0 ≤ 1-d by linarith only [du])
  have dsq : d^2≤1 := by nlinarith only [square,du]
  have remainder := mul_nonneg
    (show 0 ≤ 1-d^2 by linarith only [dsq])
    (show 0 ≤ 1+4*d^2 by positivity)
  have lower : 7/5-(2/5)*d^2 ≤ v := by
    by_contra bad
    have low : v < 7/5-(2/5)*d^2 := by exact lt_of_not_ge bad
    have product := mul_pos
      (show 0 < 7/5-(2/5)*d^2-v by linarith only [low])
      (show 0 < 7/5-(2/5)*d^2+v by linarith only [vlow,dsq])
    nlinarith only [norm,remainder,product]
  have weighted := mul_nonneg
    (show 0 ≤ 4/5-(419/1000)*d by linarith only [du])
    (show 0 ≤ v-(7/5-(2/5)*d^2) by linarith only [lower])
  have cubic := mul_nonneg dn (sq_nonneg (d-1/6))
  have certificate :
      ((4/5-(419/1000)*d)*v+(3/5)*d+(267/1000)*d^2-539/500)-
        (4/5-(419/1000)*d)*(v-(7/5-(2/5)*d^2)) =
      21/500+(419/2500)*d*(d-1/6)^2+(43/15000)*d^2+(787/90000)*d := by ring
  nlinarith only [certificate,weighted,cubic,dn,sq_nonneg d]

theorem negative_margin (c s : ℝ) (cp : 0 < c) (sn : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1) :
    0 < (7/5)*c+(1/5)*s+(419/500)*s^2-(267/500)*c*s-123/100 := by
  obtain ⟨_,cu,sumlow,_,_⟩ := CanonicalScalars.bounds c s cp sn order unit
  let d := c-s
  let v := c+s
  have dn : 0 ≤ d := sub_nonneg.mpr order
  have du : d ≤ 1 := by dsimp [d]; linarith only [cu,sn]
  have vlow : 1 ≤ v := sumlow
  have norm : v^2+d^2=2 := by dsimp [v,d]; nlinarith only [unit]
  have identity :
      (7/5)*c+(1/5)*s+(419/500)*s^2-(267/500)*c*s-123/100 =
      (4/5-(419/1000)*d)*v+(3/5)*d+(267/1000)*d^2-539/500 := by
    dsimp [d,v]
    linear_combination (19/125)*unit
  rw [identity]
  exact negative_margin_dv d v dn du vlow norm

end N12Compact.CommonCases.C702SouthScalars
