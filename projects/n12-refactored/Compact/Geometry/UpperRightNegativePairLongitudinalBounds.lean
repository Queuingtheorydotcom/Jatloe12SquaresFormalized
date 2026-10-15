import Compact.Geometry.UpperRightNegativeTopBounds
import Compact.Geometry.C977CornerSectorBounds

/-! Continuous longitudinal margins for the last northeast corner sector.
Both canonical frames have negative sine. These inequalities retain the
relative-angle order wherever it is used. Source-only; no angle sampling. -/
namespace N12Compact.UpperRightNegativePairLongitudinalBounds

open C977CornerCubic C977CornerSectorBounds
open UpperRightCornerLongitudinalBounds

theorem cosine_defect {c s : ℝ} (n : Normal c s) : 1-c≤(3/5)*s^2 := by
  have b := normal_bounds n
  have product := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤(3/5)*c-2/5 by linarith only [b.1])
  nlinarith only [product,n.2.2]

theorem forward_lower {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0<1+e*(c+s-44/25+(61/100)*s^2-(13/20)*c*s)+
      f*(s-c+13/20-(13/20)*s^2-(61/100)*c*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have arc := UpperRightNegativeTopBounds.arc tn
  have cs := mul_nonneg (show 0≤c by linarith only [tb.1]) tn.1
  have a : -(19/25)≤c+s-44/25+(61/100)*s^2-(13/20)*c*s := by
    nlinarith only [arc,cs,sq_nonneg s]
  have factor : 0≤1-(61/100)*c-(13/20)*s := by
    linarith only [tb.1,tb.2.2.2.2.2]
  have product := mul_nonneg tn.1 factor
  have b : -(7/20)≤s-c+13/20-(13/20)*s^2-(61/100)*c*s := by
    nlinarith only [product,tb.2.1]
  have first := mul_nonneg (show 0≤e by linarith only [eb.1]) (sub_nonneg.mpr a)
  have last := mul_nonneg en.1 (sub_nonneg.mpr b)
  have disk := disk_margin en (show (19/25 : ℝ)^2+(7/20)^2<1 by norm_num)
  nlinarith only [first,last,disk]

theorem forward_row {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0<1+e*(c-44/25+(33/50)*s^2)+f*(s-(33/50)*c*s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have product := mul_nonneg (sub_nonneg.mpr tb.2.1)
    (show 0≤(33/50)*c-17/50 by linarith only [tb.1])
  have a : -(19/25)≤c-44/25+(33/50)*s^2 := by
    nlinarith only [product,tn.2.2]
  have b := mul_nonneg tn.1 (show 0≤1-(33/50)*c by linarith only [tb.2.1])
  have first := mul_nonneg (show 0≤e by linarith only [eb.1]) (sub_nonneg.mpr a)
  have last := mul_nonneg en.1 b
  nlinarith only [first,last,eb.2.1]

theorem forward_upper {e f c s : ℝ} (en : Normal e f) (tn : Normal c s)
    (order : 0≤e*s-f*c) :
    0≤s+e*(1-c-(44/25)*s+c*s)+f*(s^2-s) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have fs : f≤s := sine_order tn en (by nlinarith only [order])
  have product := mul_nonneg (sub_nonneg.mpr tb.2.1)
    (sub_nonneg.mpr tb.2.2.2.1)
  have first := mul_nonneg (show 0≤e by linarith only [eb.1]) product
  have last := mul_nonneg (mul_nonneg en.1 tn.1) (sub_nonneg.mpr fs)
  have chord : e≤1-f^2/2 := by nlinarith only [en.2.2,sq_nonneg (1-e)]
  have quadratic : 0≤1-(19/25)*e-f+f^2 := by
    nlinarith only [chord,sq_nonneg (f-25/69)]
  have positive := mul_nonneg tn.1 quadratic
  nlinarith only [first,last,positive]

theorem forward_reverse_upper {e f c s : ℝ} (en : Normal e f) (tn : Normal c s)
    (order : e*s-f*c≤0) :
    0≤s+e*(1-c-(44/25)*s+c*s)+f*(s^2-s)-s*(e*s-f*c) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have sf : s≤f := sine_order en tn order
  have ec : e≤c := cosine_order en tn sf
  let A := 1-c+s*(c-s-44/25)
  let B := s*(c+s-1)
  have defect := cosine_defect tn
  have a : A≤0 := by
    have prod := mul_nonneg tn.1 (show 0≤44/25-c+(2/5)*s by
      linarith only [tb.2.1,tn.1])
    dsimp [A]; nlinarith only [defect,prod]
  have b : 0≤B := mul_nonneg tn.1 (by linarith only [tb.2.2.2.2.1])
  have first := mul_nonneg (sub_nonneg.mpr ec) (neg_nonneg.mpr a)
  have last := mul_nonneg (sub_nonneg.mpr sf) b
  have identity : s+c*A+s*B=c-1+s*(2-(44/25)*c) := by
    dsimp [A,B]
    linear_combination (s-1)*tn.2.2
  have disk := disk_margin tn (show (22/25 : ℝ)^2+(3/10)^2<1 by norm_num)
  have positive := mul_nonneg tn.1 (show 0≤2-(44/25)*c-(3/5)*s by linarith only [disk])
  have parallel : 0≤s+c*A+s*B := by nlinarith only [identity,positive,defect]
  dsimp [A,B] at first last parallel
  nlinarith only [first,last,parallel]

private theorem reverse_coefficients {e f : ℝ} (en : Normal e f) :
    e-44/25+(1/2)*f^2-(1/2)*e*f≤0 ∧
      0≤f+1/2-(1/2)*f^2-(1/2)*e*f := by
  have b := normal_bounds en
  have prod := mul_nonneg en.1 (sub_nonneg.mpr en.2.1)
  have last := mul_nonneg en.1 (show 0≤1-(e+f)/2 by linarith only [b.2.2.2.2.2])
  exact ⟨by nlinarith only [prod,b.2.1],by nlinarith only [last]⟩

theorem reverse_parallel {e f c s : ℝ} (en : Normal e f) (tn : Normal c s)
    (order : 0≤e*s-f*c) :
    0<1+c*(e-44/25+(1/2)*f^2-(1/2)*e*f)+
      s*(f+1/2-(1/2)*f^2-(1/2)*e*f) := by
  have eb := normal_bounds en
  have sf : f≤s := sine_order tn en (by nlinarith only [order])
  have ce : c≤e := cosine_order tn en sf
  have coeff := reverse_coefficients en
  have first := mul_nonneg (sub_nonneg.mpr ce) (neg_nonneg.mpr coeff.1)
  have last := mul_nonneg (sub_nonneg.mpr sf) coeff.2
  have identity : 1+e*(e-44/25+(1/2)*f^2-(1/2)*e*f)+
      f*(f+1/2-(1/2)*f^2-(1/2)*e*f)=2-(44/25)*e := by
    linear_combination (1-f/2)*en.2.2
  nlinarith only [first,last,identity,eb.2.1]

theorem reverse_parallel_top {e f c s : ℝ} (en : Normal e f) (tn : Normal c s)
    (order : 0≤e*s-f*c) :
    0≤c-1+s*(1+c*(e-44/25+(1/2)*f^2-(1/2)*e*f)+
      s*(f+1/2-(1/2)*f^2-(1/2)*e*f)) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have sf : f≤s := sine_order tn en (by nlinarith only [order])
  have defect := cosine_defect en
  have coeff : -(19/25)-(1/2)*f-(1/10)*f^2≤
      e-44/25+(1/2)*f^2-(1/2)*e*f := by
    have prod := mul_nonneg en.1 (sub_nonneg.mpr eb.2.1)
    nlinarith only [defect,prod]
  have other : 1/2+(7/25)*f≤f+1/2-(1/2)*f^2-(1/2)*e*f := by
    have prod := mul_nonneg en.1
      (show 0≤18/25-(e+f)/2 by linarith only [eb.2.2.2.2.2])
    nlinarith only [prod]
  have first := mul_nonneg (show 0≤c by linarith only [tb.1]) (sub_nonneg.mpr coeff)
  have last := mul_nonneg tn.1 (sub_nonneg.mpr other)
  have replaceLinear := mul_nonneg (sub_nonneg.mpr sf)
    (show 0≤c/2-(7/25)*s by nlinarith only [tn.2.1,tb.1])
  have squares := mul_nonneg (sub_nonneg.mpr sf) (add_nonneg en.1 tn.1)
  have replaceSquare := mul_nonneg (show 0≤c/10 by linarith only [tb.1]) squares
  have cChord : c≤1-s^2/2 := by nlinarith only [tn.2.2,sq_nonneg (1-c)]
  have mixed := mul_nonneg tn.1 (sub_nonneg.mpr tb.2.1)
  have cubic := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr tb.2.1)
  have lower : (3/5)*s≤1+c*(e-44/25+(1/2)*f^2-(1/2)*e*f)+
      s*(f+1/2-(1/2)*f^2-(1/2)*e*f) := by
    have square := sq_nonneg (s-15/28)
    nlinarith only [first,last,replaceLinear,replaceSquare,cChord,mixed,cubic,square]
  have scaled := mul_nonneg tn.1 (sub_nonneg.mpr lower)
  have wall := cosine_defect tn
  nlinarith only [scaled,wall]

theorem reverse_row {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0<1+c*(e-63/50-e^2/2)+s*f*(1-e/2) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have chord := mul_nonneg (sub_nonneg.mpr eb.1) (sub_nonneg.mpr eb.2.1)
  have bound : 91/200≤e-e^2/2 := by nlinarith only [chord,eb.1]
  have first := mul_nonneg (show 0≤c by linarith only [tb.1]) (sub_nonneg.mpr bound)
  have last := mul_nonneg (mul_nonneg tn.1 en.1)
    (show 0≤1-e/2 by linarith only [eb.2.1])
  nlinarith only [first,last,tb.2.1]

theorem reverse_row_top {e f c s : ℝ} (en : Normal e f) (tn : Normal c s) :
    0≤c-1+s*(1+c*(e-63/50-e^2/2)+s*f*(1-e/2)) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have chord := mul_nonneg (sub_nonneg.mpr eb.1) (sub_nonneg.mpr eb.2.1)
  have bound : 91/200≤e-e^2/2 := by nlinarith only [chord,eb.1]
  have first := mul_nonneg (show 0≤c by linarith only [tb.1]) (sub_nonneg.mpr bound)
  have last := mul_nonneg (mul_nonneg tn.1 en.1)
    (show 0≤1-e/2 by linarith only [eb.2.1])
  have lower : 1-(161/200)*c≤1+c*(e-63/50-e^2/2)+s*f*(1-e/2) := by
    nlinarith only [first,last]
  have defectProduct := mul_nonneg (sub_nonneg.mpr tb.2.1)
    (show 0≤(59/100)*c-41/100 by linarith only [tb.1])
  have defect : 1-c≤(59/100)*s^2 := by nlinarith only [defectProduct,tn.2.2]
  have disk := disk_margin tn (show (161/200 : ℝ)^2+(59/100)^2<1 by norm_num)
  have boundScaled := mul_nonneg tn.1 (sub_nonneg.mpr lower)
  have diskScaled := mul_nonneg tn.1 (le_of_lt disk)
  nlinarith only [defect,boundScaled,diskScaled]

end N12Compact.UpperRightNegativePairLongitudinalBounds
