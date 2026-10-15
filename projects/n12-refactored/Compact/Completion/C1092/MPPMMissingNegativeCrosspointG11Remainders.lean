import Compact.Completion.C1092.MPPMCrosspointBoundaryHalf

/-! Three constant quadratic-arc remainders for the missing-negative
G11 proof. All boxes are closed. The middle interval uses one completed
square and ordinary product bounds, without angular differentiation. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointSupport
open C1092MPPMCrosspointSupport C1092MPPMCrosspointSupport.QuadraticArc
set_option Elab.async false

private theorem zero_formula (a b C z r : ℝ) :
    remainder a b C 0 z r=(a-C)+(-a-C)*(z^2+r^2+z^2*r^2)-2*a*z*r+2*b*(z+r) := by
  dsimp [remainder,X,Y,Z,sum3,pair3,triple3]
  ring

theorem low_remainder (z : ℝ) (zn : 0≤z) (zu : z≤1/3) :
    0≤remainder (67/200) (-(147/200)) (-(123/100)) 0 z (1/3) := by
  have extra : 0≤z^2+(1/3:ℝ)^2+z^2*(1/3:ℝ)^2 := by positivity
  rw [zero_formula]
  nlinarith only [extra,zu]

theorem high_remainder (z r : ℝ) (zn : 0≤z) (zu : z≤5/12)
    (rn : 0≤r) (ru : r≤5/12) :
    0≤remainder (173/200) (-(101/200)) (-(311/200)) 0 z r := by
  have product := mul_le_mul zu ru rn (by norm_num : (0:ℝ)≤5/12)
  have extra : 0≤z^2+r^2+z^2*r^2 := by positivity
  rw [zero_formula]
  nlinarith only [product,extra,zu,ru]

theorem middle_remainder (q z r : ℝ)
    (ql : 1/3≤q) (qu : q≤5/12) (zl : 1/3≤z) (zu : z≤5/12)
    (rl : 1/3≤r) (ru : r≤5/12) :
    0≤remainder (-(33/40)) (-(171/200)) (-(123/100)) q z r := by
  have qn : 0≤q := by linarith only [ql]
  have zn : 0≤z := by linarith only [zl]
  have rn : 0≤r := by linarith only [rl]
  have qz := mul_le_mul ql zl (by norm_num : (0:ℝ)≤1/3) qn
  have qr := mul_le_mul ql rl (by norm_num : (0:ℝ)≤1/3) qn
  have zr := mul_le_mul zl rl (by norm_num : (0:ℝ)≤1/3) zn
  have Pn : 1/3≤pair3 q z r := by dsimp [pair3]; nlinarith only [qz,qr,zr]
  have Psquare := mul_nonneg (show 0≤pair3 q z r-1/3 by linarith only [Pn])
    (show 0≤pair3 q z r+1/3 by linarith only [Pn])
  have upper0 := mul_le_mul qu zu zn (by norm_num : (0:ℝ)≤5/12)
  have upper1 := mul_le_mul upper0 ru rn (by norm_num : (0:ℝ)≤(5/12)*(5/12))
  have Rn : 0≤triple3 q z r := by dsimp [triple3]; positivity
  have Ru : triple3 q z r≤125/1728 := by dsimp [triple3]; nlinarith only [upper1]
  have Rsquare := mul_le_mul Ru Ru Rn (by norm_num : (0:ℝ)≤125/1728)
  have qq := mul_le_mul ql ql (by norm_num : (0:ℝ)≤1/3) qn
  have zz := mul_le_mul zl zl (by norm_num : (0:ℝ)≤1/3) zn
  have rr := mul_le_mul rl rl (by norm_num : (0:ℝ)≤1/3) rn
  have Q : 10/9≤1+q^2 := by nlinarith only [qq]
  have Z' : 10/9≤1+z^2 := by nlinarith only [zz]
  have R : 10/9≤1+r^2 := by nlinarith only [rr]
  have lower0 := mul_le_mul Q Z' (by norm_num : (0:ℝ)≤10/9) (by positivity)
  have lower1 := mul_le_mul lower0 R (by norm_num : (0:ℝ)≤10/9) (by positivity)
  have Zlow : 1000/729≤Z q z r := by dsimp [Z]; nlinarith only [lower1]
  have RP := mul_nonneg Rn (show 0≤pair3 q z r by linarith only [Pn])
  have square := sq_nonneg (sum3 q z r-57/55)
  dsimp [remainder,X,Y]
  nlinarith only [Psquare,Rsquare,Zlow,RP,square]

end N12Compact.C1092MPPMMissingNegativeCrosspointSupport
