import S12.ShortCluster
import S12.Diagonal

/-! The positive mixed-neighbor point in C983-F4-FULL-8208-ENDING.
A coarse exact sine bound suffices for the last target band, avoiding
differentiation and sampled orientations. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false

theorem positive_mixed_transfer (N : OpenSquare) (side : 1 < N.side)
    (cp : 0 < N.c) (sn : 0 ≤ N.s) (order : N.s ≤ N.c)
    (f : N.Inside 0 (13/50)) (g : N.Inside (13/50) 1)
    (missingO : ¬N.Inside 0 0) (missingP : ¬N.Inside 0 1)
    (missingD : ¬N.Inside (13/50) 0) : N.Inside (1/2) 1 := by
  have cu : N.c ≤ 1 := by
    nlinarith only [N.unit_normal,sq_nonneg N.s,sq_nonneg (N.c-1)]
  have su : N.s ≤ 1 := by
    nlinarith only [N.unit_normal,sq_nonneg N.c,sq_nonneg (N.s-1)]
  have hf := f
  have hg := g
  simp only [OpenSquare.Inside,InBands,mul_zero,mul_one,zero_mul,zero_add,add_zero] at hf hg
  have upper : N.loV+N.side ≤ N.c := by
    apply le_of_not_gt
    intro high
    apply missingP
    simp only [OpenSquare.Inside,InBands,mul_zero,mul_one,zero_mul,zero_add,add_zero]
    refine ⟨?_,?_,?_,high⟩ <;> linarith only [hf.1,hf.2.2.1,hg.2.1,cp,sn]
  have lower : -(13/50)*N.s ≤ N.loV := by
    apply le_of_not_gt
    intro low
    apply missingD
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [hf.1,hg.2.1,hg.2.2.2,low,cp,sn,order]
  have span : 1 < N.c+(13/50)*N.s := by linarith only [upper,lower,side]
  have sp : 0 < N.s := by linarith only [span,cu]
  have shallow : N.s < 1/2 := by
    by_contra high
    have positiveBase : 0 < 1-(13/50)*N.s := by linarith only [su]
    have strict := mul_pos
      (show 0 < N.c-(1-(13/50)*N.s) by linarith only [span])
      (show 0 < N.c+(1-(13/50)*N.s) by linarith only [cp,positiveBase])
    have correction := mul_nonneg sn
      (show 0 ≤ (2669/2500)*N.s-13/25 by linarith only [high])
    nlinarith only [N.unit_normal,strict,correction]
  have originV : N.loV < 0 := by linarith only [upper,side,cu]
  have originFace : 0 ≤ N.loU := by
    apply le_of_not_gt
    intro low
    apply missingO
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero]
    refine ⟨low,?_,originV,?_⟩ <;> linarith only [hf.2.1,hf.2.2.2,sp,cp]
  have targetUpperU : N.c*(1/2)+N.s < N.loU+N.side := by
    linarith only [originFace,side,cu,shallow]
  simp only [OpenSquare.Inside,InBands,mul_one]
  refine ⟨?_,targetUpperU,?_,?_⟩
  · linarith only [hg.1,cp]
  · linarith only [upper,side,su]
  · linarith only [hg.2.2.2,sp]

/-- The actual positive mixed C983 northeast owner inherits its target
from the three displayed foreign owners; none is invented for an omitted
auxiliary. -/
theorem positive_mixed_original (N W T E : OpenSquare)
    (side : 1 < N.side) (cp : 0 < N.c)
    (sn : 0 ≤ N.s) (order : N.s ≤ N.c)
    (f : N.Inside 2 (113/50)) (g : N.Inside (113/50) 3)
    (wCenter : W.Inside 2 2) (tOrigin : T.Inside 2 3)
    (eElbow : E.Inside (113/50) 2)
    (apartNW : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y))
    (apartNT : ∀ x y, ¬(N.Inside x y ∧ T.Inside x y))
    (apartNE : ∀ x y, ¬(N.Inside x y ∧ E.Inside x y)) :
    N.Inside (5/2) 3 := by
  have missingO : ¬N.Inside 2 2 := fun h => apartNW _ _ ⟨h,wCenter⟩
  have missingP : ¬N.Inside 2 3 := fun h => apartNT _ _ ⟨h,tOrigin⟩
  have missingD : ¬N.Inside (113/50) 2 := fun h => apartNE _ _ ⟨h,eElbow⟩
  have result := positive_mixed_transfer (N.translated 2 2) side cp sn order
    (by norm_num [inside_translated_iff]; exact f)
    (by norm_num [inside_translated_iff]; exact g)
    (by norm_num [inside_translated_iff]; exact missingO)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingD)
  norm_num [inside_translated_iff] at result
  exact result

#print axioms positive_mixed_original
end N12Compact.Completion.OtherCases.C983

