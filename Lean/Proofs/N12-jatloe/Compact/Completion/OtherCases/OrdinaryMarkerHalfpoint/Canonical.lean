import Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint.Inputs
import Compact.Completion.CommonCases.CanonicalScalars

/-! The actual forced faces for every offset and both canonical signs.
All four omitted points are separate; no wall or upper-side bound is added. -/
namespace N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint
open S12 S12Pilot
set_option Elab.async false

theorem positive (q : OpenSquare) (d : ℝ) (h : Input q d)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c) : q.Inside 1 (-1/2) := by
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have m := h.marker
  have a := h.near
  have b := h.far
  have dc := mul_nonneg h.offsetNonnegative cp.le
  have ds := mul_nonneg h.offsetNonnegative sn
  have dcUpper := mul_nonneg cp.le (sub_nonneg.mpr h.offsetUpper)
  have dsUpper := mul_nonneg sn (sub_nonneg.mpr h.offsetUpper)
  have lowerV : -q.s-q.c≤q.loV := by
    apply le_of_not_gt
    intro low
    apply h.missingCorner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [m.1,b.2.1,b.2.2.2,cp,sn,order,low]
  have rLowerU : q.loU<(1+d)*q.c := by nlinarith only [m.1,dc,cp,sn]
  have rLowerV : q.loV< -(1+d)*q.s := by
    nlinarith only [b.2.2.1,dsUpper,cp,order]
  have rUpperV : -(1+d)*q.s<q.loV+q.side := by
    nlinarith only [lowerV,h.side,cu,ds]
  have upperU : q.loU+q.side≤(1+d)*q.c := by
    apply le_of_not_gt
    intro high
    apply h.missingRight
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [rLowerU,high,rLowerV,rUpperV]
  have dLowerU : q.loU<(13/50)*q.c := by
    nlinarith only [upperU,h.side,cu,dcUpper]
  have dUpperU : (13/50)*q.c<q.loU+q.side := by
    linarith only [a.2.1,cp,order]
  have dLowerV : q.loV< -(13/50)*q.s := by
    linarith only [m.2.2.1,cp,sn]
  have upperV : q.loV+q.side≤ -(13/50)*q.s := by
    apply le_of_not_gt
    intro high
    apply h.missingInward
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [dLowerU,dUpperU,dLowerV,high]
  have short := (short_projections q (37/50) (-1/2) (by norm_num)).2.2.1
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [m.1,b.2.1,b.2.2.2,upperV,h.side,short,cp,sn,order]

private theorem negative_bands (q : OpenSquare) (s : ℝ) (signed : q.s= -s)
    (x y : ℝ) : q.Inside x y ↔
      q.loU<q.c*x-s*y ∧ q.c*x-s*y<q.loU+q.side ∧
      q.loV<s*x+q.c*y ∧ s*x+q.c*y<q.loV+q.side := by
  simp only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,sub_eq_add_neg]

theorem negative_lower_impossible (q : OpenSquare) (d s : ℝ) (h : Input q d)
    (signed : q.s= -s) (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c)
    (lowerY : s-q.c/2≤q.loV) : False := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu := (CommonCases.CanonicalScalars.bounds q.c s cp sn order unit).2.1
  have bands := negative_bands q s signed
  have m := (bands _ _).mp h.marker
  have b := (bands _ _).mp h.far
  have dc := mul_nonneg h.offsetNonnegative cp.le
  have ds := mul_nonneg h.offsetNonnegative sn
  have dcUpper := mul_nonneg cp.le (sub_nonneg.mpr h.offsetUpper)
  have dLowerV : q.loV<(13/50)*s := by linarith only [m.2.2.1,cp,order]
  have dUpperU : (13/50)*q.c<q.loU+q.side := by linarith only [m.2.1,cp,sn]
  have dUpperV : (13/50)*s<q.loV+q.side := by
    linarith only [lowerY,h.side,cu,sn]
  have lowerU : (13/50)*q.c≤q.loU := by
    apply le_of_not_gt
    intro low
    apply h.missingInward
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,dUpperU,dLowerV,dUpperV]
  have rLowerU : q.loU<(1+d)*q.c := by nlinarith only [m.1,cp,order,dc]
  have rLowerV : q.loV<(1+d)*s := by nlinarith only [b.2.2.1,cp,ds]
  have diameter : d^2+(1/2)^2≤1 := by
    have bound := mul_nonneg (sub_nonneg.mpr h.offsetUpper)
      (show 0≤13/50+d by linarith only [h.offsetNonnegative])
    nlinarith only [bound]
  have short := (short_projections q d (1/2) diameter).2.2.2
  rw [signed,neg_neg] at short
  have rUpperV : (1+d)*s<q.loV+q.side := by
    nlinarith only [lowerY,h.side,short]
  have upperU : q.loU+q.side≤(1+d)*q.c := by
    apply le_of_not_gt
    intro high
    apply h.missingRight
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [rLowerU,high,rLowerV,rUpperV]
  nlinarith only [upperU,lowerU,h.side,cu,dcUpper]

theorem negative_upper_impossible (q : OpenSquare) (d s : ℝ) (h : Input q d)
    (signed : q.s= -s) (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c)
    (upperY : q.loU+q.side≤q.c+s/2) : False := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu := (CommonCases.CanonicalScalars.bounds q.c s cp sn order unit).2.1
  have bands := negative_bands q s signed
  have m := (bands _ _).mp h.marker
  have b := (bands _ _).mp h.far
  have short := (short_projections q (37/50) (-1/2) (by norm_num)).2.1
  rw [signed] at short
  have dLowerU : q.loU<(13/50)*q.c := by nlinarith only [upperY,h.side,short]
  have dUpperU : (13/50)*q.c<q.loU+q.side := by linarith only [m.2.1,cp,sn]
  have dLowerV : q.loV<(13/50)*s := by linarith only [m.2.2.1,cp,order]
  have upperV : q.loV+q.side≤(13/50)*s := by
    apply le_of_not_gt
    intro high
    apply h.missingInward
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [dLowerU,dUpperU,dLowerV,high]
  have kLowerU : q.loU<q.c+s := by linarith only [m.1,cp,sn]
  have kLowerV : q.loV<s-q.c := by linarith only [upperV,h.side,cu,sn]
  have kUpperV : s-q.c<q.loV+q.side := by linarith only [m.2.2.2,order]
  have upperK : q.loU+q.side≤q.c+s := by
    apply le_of_not_gt
    intro high
    apply h.missingCorner
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [kLowerU,high,kLowerV,kUpperV]
  have fLowerU : q.loU<(13/50)*q.c+s := by linarith only [upperK,h.side,cu]
  have fLowerV : q.loV<(13/50)*s-q.c := by linarith only [upperV,h.side,cu]
  have fUpperV : (13/50)*s-q.c<q.loV+q.side := by linarith only [m.2.2.2,cp,sn]
  have upperF : q.loU+q.side≤(13/50)*q.c+s := by
    apply le_of_not_gt
    intro high
    apply h.missingLower
    apply (bands _ _).mpr
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowerU,high,fLowerV,fUpperV]
  linarith only [b.2.1,upperF,order,cp]

theorem negative (q : OpenSquare) (d s : ℝ) (h : Input q d)
    (signed : q.s= -s) (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c) :
    q.Inside 1 (-1/2) := by
  by_cases lowerY : s-q.c/2≤q.loV
  · exact False.elim (negative_lower_impossible q d s h signed cp sn order lowerY)
  by_cases upperY : q.loU+q.side≤q.c+s/2
  · exact False.elim (negative_upper_impossible q d s h signed cp sn order upperY)
  have bands := negative_bands q s signed
  have m := (bands _ _).mp h.marker
  have b := (bands _ _).mp h.far
  apply (bands _ _).mpr
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [m.1,b.2.2.2,cp,sn,lowerY,upperY]

end N12Compact.Completion.OtherCases.OrdinaryMarkerHalfpoint
