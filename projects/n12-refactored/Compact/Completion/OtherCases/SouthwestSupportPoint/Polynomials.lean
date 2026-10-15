import Compact.Completion.CommonCases.BernsteinQuartic

/-! All five exact quartics and all five closed-interval coefficient
identities from C974-C976-SW-SUPPORT-POINT.md section 7. The displayed
source coefficients are rational; no angle samples or generated forest
are used. This source has not been compiled. -/
namespace N12Compact.Completion.OtherCases.SouthwestSupportPoint.Polynomials
open CommonCases.BernsteinQuartic
set_option Elab.async false

def p1 (t : ℝ) : ℝ := (35+926*t-654*t^2-11326*t^3-8765*t^4)/100
def p2 (t : ℝ) : ℝ := (-199+2026*t+3614*t^2+1574*t^3-7199*t^4)/100
def p3 (t : ℝ) : ℝ := (1-4*t-17*t^2+104*t^3-49*t^4)/25
def p4 (t : ℝ) : ℝ := (35-206*t+4946*t^2+10606*t^3-8765*t^4)/100
def p5 (t : ℝ) : ℝ := (35-674*t+1306*t^2+11074*t^3-8765*t^4)/100

theorem p1_positive (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ 1/7) : 0 < p1 t := by
  let z := 7*t
  have zn : 0 ≤ z := by dsimp only [z]; linarith only [lo]
  have zu : z ≤ 1 := by dsimp only [z]; linarith only [hi]
  have certificate : p1 t = value z (7/20) (953/1400) (4847/4900)
      (167/140) (14078/12005) := by dsimp only [p1,z,value]; ring
  rw [certificate]
  exact positive _ _ _ _ _ _ zn zu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem p2_positive (t : ℝ) (lo : 1/8 ≤ t) (hi : t ≤ 5/12) : 0 < p2 t := by
  let z := (24*t-3)/7
  have zn : 0 ≤ z := by dsimp only [z]; linarith only [lo]
  have zu : z ≤ 1 := by dsimp only [z]; linarith only [hi]
  have certificate : p2 t = value z (458897/409600) (2008619/614400)
      (16363519/2764800) (12362191/1382400) (24250201/2073600) := by
    dsimp only [p2,z,value]; ring
  rw [certificate]
  exact positive _ _ _ _ _ _ zn zu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem p3_positive (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ 1/3) : 0 < p3 t := by
  let z := 3*t
  have zn : 0 ≤ z := by dsimp only [z]; linarith only [lo]
  have zu : z ≤ 1 := by dsimp only [z]; linarith only [hi]
  have certificate : p3 t = value z (1/25) (2/75) (1/1350) (1/1350) (83/2025) := by
    dsimp only [p3,z,value]; ring
  rw [certificate]
  exact positive _ _ _ _ _ _ zn zu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem p4_positive (t : ℝ) (lo : 0 ≤ t) (hi : t ≤ 5/12) : 0 < p4 t := by
  let z := (12/5)*t
  have zn : 0 ≤ z := by dsimp only [z]; linarith only [lo]
  have zu : z ≤ 1 := by dsimp only [z]; linarith only [hi]
  have certificate : p4 t = value z (7/20) (13/96) (11681/8640)
      (409031/69120) (5436479/414720) := by dsimp only [p4,z,value]; ring
  rw [certificate]
  exact positive _ _ _ _ _ _ zn zu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem p5_positive (t : ℝ) (lo : 4/25 ≤ t) (hi : t ≤ 5/12) : 0 < p5 t := by
  let z := (300*t-48)/77
  have zn : 0 ≤ z := by dsimp only [z]; linarith only [lo]
  have zu : z ≤ 1 := by dsimp only [z]; linarith only [hi]
  have certificate : p5 t = value z (16287/7812500) (10925491/37500000)
      (31314797/27000000) (24524261/8640000) (429475/82944) := by
    dsimp only [p5,z,value]; ring
  rw [certificate]
  exact positive _ _ _ _ _ _ zn zu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end N12Compact.Completion.OtherCases.SouthwestSupportPoint.Polynomials
