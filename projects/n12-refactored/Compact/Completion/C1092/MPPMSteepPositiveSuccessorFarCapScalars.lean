import Compact.Completion.C1092.MPPMPositiveRetainingSteepScalars
import Compact.Completion.C1092.MMMP.UpperThirdScalars

/-! Rational bounds for STEEP-POSITIVE-SUCCESSOR-FAR-CAP.  The small
relative-angle estimate uses the unit-circle identity, and the wall-exit
bound uses an exact quadratic product. No angle mesh is used. -/
namespace N12Compact.C1092MPPMSteepPositiveSuccessorFarCap.Scalars
open C977CornerCubic C1092MPPMPositiveRetainingSteep.Scalars
set_option Elab.async false

theorem central_bounds {c s a U V : ℝ} (cn : Normal c s)
    (steep : 3/5≤s) (side : 1<a) (lowU : -c-s≤U)
    (lowV : (14/25)*s-c≤V) (highV : V+a≤(543/500)*s) :
    -(83/200)<U+a ∧ 67/125<V+a ∧ V+a<96/125 ∧ 29/125< -V := by
  have cb := normal_bounds cn
  have cosine := C1092MMMPUpperThirdScalars.cosine_cap cn steep
  have sum : c+s<283/200 := by
    apply lt_of_not_ge
    intro no
    have square := mul_nonneg (show 0≤c+s-283/200 by linarith only [no])
      (show 0≤c+s+283/200 by linarith only [cb.1,cn.1])
    nlinarith only [square,sq_nonneg (c-s),cn.2.2]
  have order := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤c+s by linarith only [cb.1,cn.1])
  have cap : (543/500)*s<96/125 := by
    apply lt_of_not_ge
    intro no
    have square := mul_nonneg (show 0≤(543/500)*s-96/125 by linarith only [no])
      (show 0≤(543/500)*s+96/125 by linarith only [cn.1])
    nlinarith only [square,order,cn.2.2]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [sum,cosine,steep,side,lowU,lowV,highV,cap]

theorem wall_width {d t : ℝ} (en : Normal d t) : t+(14/25)*d<138/125 := by
  have eb := normal_bounds en
  have product := mul_nonneg (sub_nonneg.mpr en.2.1)
    (show 0≤1129*d-271*t by linarith only [en.2.1,eb.1])
  apply lt_of_not_ge
  intro no
  have square := mul_nonneg (show 0≤t+(14/25)*d-138/125 by linarith only [no])
    (show 0≤t+(14/25)*d+138/125 by linarith only [eb.1,en.1])
  nlinarith only [product,square,en.2.2]

theorem close_order {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (steep : 3/5≤s) (order : 0≤sigma c s d t) :
    49/50<kappa c s d t ∧ sigma c s d t<3/20 := by
  have cosine := C1092MMMPUpperThirdScalars.cosine_cap cn steep
  have eb := canonical_bounds en
  have rel := relative_bounds cn en
  have first := mul_nonneg cn.1 (sub_nonneg.mpr en.2.1)
  have last := mul_nonneg en.1 (show 0≤1/5-(c-s) by linarith only [cosine,steep])
  have small : sigma c s d t<3/20 := by
    dsimp [sigma]
    nlinarith only [first,last,eb.2.2.2.1]
  have square := mul_pos (show 0<3/20-sigma c s d t by linarith only [small])
    (show 0<3/20+sigma c s d t by linarith only [order])
  have unit := relative_unit cn en
  have large : 49/50<kappa c s d t := by
    apply lt_of_not_ge
    intro no
    have bound := mul_nonneg (show 0≤49/50-kappa c s d t by linarith only [no])
      (show 0≤49/50+kappa c s d t by linarith only [rel.1])
    nlinarith only [bound,square,unit]
  exact ⟨large,small⟩

theorem earlier_weight {c s d t : ℝ} (cn : Normal c s) (en : Normal d t)
    (order : sigma c s d t≤0) :
    11/25≤(11/25)*kappa c s d t-sigma c s d t := by
  have rel := relative_bounds cn en
  have unit := relative_unit cn en
  have product := mul_nonneg (show 0≤kappa c s d t by linarith only [rel.1])
    (neg_nonneg.mpr order)
  have sum : 1≤kappa c s d t-sigma c s d t := by
    apply le_of_not_gt
    intro no
    have square := mul_pos (show 0<1-(kappa c s d t-sigma c s d t) by linarith only [no])
      (show 0<1+(kappa c s d t-sigma c s d t) by linarith only [rel.1,order])
    nlinarith only [square,product,unit]
  linarith only [sum,order]

end N12Compact.C1092MPPMSteepPositiveSuccessorFarCap.Scalars
