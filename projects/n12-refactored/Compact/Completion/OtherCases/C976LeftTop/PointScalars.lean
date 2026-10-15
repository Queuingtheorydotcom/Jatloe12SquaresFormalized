import Compact.Completion.OtherCases.C976LeftTop.PointInputs
import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.C1092.WallProfileScalars

/-! Exact scalar steps in C976-LEFT-UPPER-POINTS. The cubic is the
printed half-angle identity; endpoint comparisons are whole-interval
unit-circle identities, without sampling or calculus imports. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
open C1092WallProfileScalars
set_option Elab.async false

private theorem endpoint (c s m n k z : ℝ) (unit : c^2+s^2=1)
    (comparison : z≤k*(m*c+n*s)) (margin : k^2*(m^2+n^2)<1) : z<1 := by
  have identity : (m*c+n*s)^2+(n*c-m*s)^2=m^2+n^2 := by
    calc
      _=(m^2+n^2)*(c^2+s^2) := by ring
      _=m^2+n^2 := by rw [unit]; ring
  have norm : (m*c+n*s)^2≤m^2+n^2 := by
    nlinarith only [identity,sq_nonneg (n*c-m*s)]
  have weighted := mul_le_mul_of_nonneg_left norm (sq_nonneg k)
  have square : (k*(m*c+n*s))^2<1 := by nlinarith only [weighted,margin]
  have small : k*(m*c+n*s)<1 := by
    nlinarith only [square,sq_nonneg (k*(m*c+n*s)-1)]
  exact lt_of_le_of_lt comparison small

theorem upper_v_span (c s : ℝ) (unit : c^2+s^2=1) (slope : (21/65)*c≤s) :
    (26/25)*c+(1/50)*s<1 := by
  apply endpoint c s 65 21 (3401/233300) ((26/25)*c+(1/50)*s) unit
  · linarith only [slope]
  · norm_num

theorem inward_span (c s : ℝ) (unit : c^2+s^2=1) : (21/25)*c+(27/100)*s<1 := by
  apply endpoint c s (21/25) (27/100) 1 ((21/25)*c+(27/100)*s) unit
  · linarith
  · norm_num

theorem small_corner_margin (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (order : s≤c) (unit : c^2+s^2=1) (small : s≤(21/65)*c) :
    1<c+(3/20)*c*s+(7/20)*s^2 := by
  have data := quarter_data c s cp.le sp.le unit
  have cu := (CommonCases.CanonicalScalars.bounds c s cp sp.le order unit).2.1
  let z := half c s
  have zp : 0<z := div_pos sp (by linarith only [cp])
  have relation : z*(1+c)=s := data.2.2.1
  have zu : z≤8/25 := by
    apply le_of_not_gt
    intro large
    have product := mul_pos (sub_pos.mpr large) (show 0<1+c by linarith only [cp])
    nlinarith only [product,relation,small,cu]
  have polynomial : 0<3-6*z-3*z^2-20*z^3 := by
    have product := mul_nonneg (sub_nonneg.mpr zu)
      (show 0≤6+3*(8/25+z)+20*((8/25)^2+(8/25)*z+z^2) by positivity)
    have identity : 3-6*z-3*z^2-20*z^3=
        367/3125+(8/25-z)*(6+3*(8/25+z)+20*((8/25)^2+(8/25)*z+z^2)) := by ring
    linarith only [identity,product]
  have den : 1+z^2≠0 := ne_of_gt (by positivity)
  have cf : c=(1-z^2)/(1+z^2) :=
    (eq_div_iff den).mpr (by nlinarith only [data.2.2.2.1])
  have sf : s=2*z/(1+z^2) :=
    (eq_div_iff den).mpr (by nlinarith only [data.2.2.2.2])
  have identity : 10*(1+z^2)^2*(c+(3/20)*c*s+(7/20)*s^2-1)=
      z*(3-6*z-3*z^2-20*z^3) := by
    rw [cf,sf]
    field_simp [den] <;> ring
  have positive := mul_pos zp polynomial
  have scaled : 0<10*(1+z^2)^2*(c+(3/20)*c*s+(7/20)*s^2-1) := by
    rw [identity]
    exact positive
  have result := (mul_pos_iff_of_pos_left (show 0<10*(1+z^2)^2 by positivity)).mp scaled
  linarith only [result]

/-- The farther-point margin also supplies the nearer point. This is the
chapter's decreasing scalar written as an exact two-point circle difference. -/
theorem farther_margin (c s : ℝ) (cp : 0<c) (sp : 0<s)
    (unit : c^2+s^2=1) (low : (37/65)*c≤s) (high : s≤(3/4)*c) :
    0<(37/100)*c+(11/100)*s-189/625-(91/2500)*c^2-(42/625)*c*s := by
  have ordering := mul_nonneg (show 0≤3*c-4*s by linarith only [high])
    (show 0≤3*c+4*s by linarith only [cp,sp])
  have cLow : 4/5≤c := by nlinarith only [unit,ordering,cp]
  have sHigh : s≤3/5 := by nlinarith only [unit,ordering,sp]
  have cHigh : c≤1 := by nlinarith only [unit,sq_nonneg s,cp]
  have circle : (c+4/5)*(c-4/5)=(3/5-s)*(s+3/5) := by nlinarith only [unit]
  have average : (c+4/5)/2≤s+3/5 := by linarith only [low,cp]
  have weight := mul_nonneg (sub_nonneg.mpr sHigh) (sub_nonneg.mpr average)
  have step : (3/5-s)/2≤c-4/5 := by
    apply (mul_le_mul_left (show 0<c+4/5 by linarith only [cp])).mp
    nlinarith only [circle,weight]
  let A := 37/100-(91/2500)*(c+4/5)-(42/625)*s
  let B : ℝ := 11/100-(42/625)*(4/5)
  have aBound : 1/4≤A := by dsimp only [A]; linarith only [cHigh,sHigh]
  have bBound : B≤3/50 := by norm_num [B]
  have first := mul_nonneg (sub_nonneg.mpr cLow) (sub_nonneg.mpr aBound)
  have last := mul_nonneg (sub_nonneg.mpr sHigh) (sub_nonneg.mpr bBound)
  have identity : (37/100)*c+(11/100)*s-189/625-(91/2500)*c^2-(42/625)*c*s=
      253/62500+(c-4/5)*A-(3/5-s)*B := by dsimp only [A,B]; ring
  nlinarith only [identity,first,last,step,sHigh]

end N12Compact.Completion.OtherCases.C976LeftTop.UpperPoints
