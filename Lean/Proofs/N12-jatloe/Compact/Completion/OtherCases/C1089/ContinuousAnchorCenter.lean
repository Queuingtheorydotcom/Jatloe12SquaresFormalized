import Compact.Completion.OtherCases.C1089.ContinuousAnchorSupport
import S12.ShortCluster.Projections

/-! INWARD-EXTENDED-ANCHOR-CENTER, Theorem 1. All four central points
and both wall points are strict, the excluded upper point is weak, and
the two squares are the actual congruent disjoint owners. Only W has a
wall and a center-sign premise. No side upper bound is used.
This completed manuscript argument is translated source, not yet compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousAnchorCenter
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private theorem positive_impossible (C W : OpenSquare) (cn : Normal C.c C.s)
    (side : 1<C.side) (M : C.Inside (7/20) (7/20))
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (A : ¬C.Inside (2/5) 1) (T : W.Inside 1 (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have lowerV : -C.s+(13/50)*C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    apply apart 1 (13/50)
    refine ⟨?_,T⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [Q.1,R.2.1,R.2.2.2,low,cp,cn.1,cn.2.1]
  have upperV : C.loV+C.side≤C.c-(2/5)*C.s := by
    apply le_of_not_gt
    intro high
    apply A
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [M.1,M.2.2.1,R.2.1,high,cp,cn.1,cn.2.1]
  have short := short_projections C (37/50) (3/5) (by norm_num)
  linarith only [lowerV,upperV,side,short.2.1]

/-- The canonical sign, both relative angle orders, and both actual SAT
sources have all been exhausted before concluding strict center ownership. -/
theorem point (C W : OpenSquare) (side : 1<C.side) (same : C.side=W.side)
    (M : C.Inside (7/20) (7/20)) (P : C.Inside 0 (13/50))
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (A : ¬C.Inside (2/5) 1)
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y,W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) : C.Inside 0 0 := by
  classical
  obtain ⟨V,cp,canon,shape,inside,_⟩ := ClosedFrames.canonical_frame C
  have ha : 1<V.side := by rwa [shape]
  have actualApart : ∀ x y,¬(V.Inside x y ∧ W.Inside x y) :=
    fun x y own => apart x y ⟨(inside _ _).mp own.1,own.2⟩
  have vM := (inside _ _).mpr M
  have vP := (inside _ _).mpr P
  have vQ := (inside _ _).mpr Q
  have vR := (inside _ _).mpr R
  by_cases sign : 0≤V.s
  · have cn : Normal V.c V.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canon,V.unit_normal⟩
    exact False.elim (positive_impossible V W cn ha vM vQ vR
      (fun own => A ((inside _ _).mp own)) T actualApart)
  · have sign : V.s<0 := lt_of_not_ge sign
    have cn : Normal V.c (-V.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_neg sign] using canon,by nlinarith only [V.unit_normal]⟩
    by_contra missing
    have lowerV : 0≤V.loV := by
      apply le_of_not_gt
      intro low
      apply missing
      apply (inside 0 0).mp
      simp only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero]
      refine ⟨?_,?_,low,?_⟩ <;>
        linarith only [vP.1,vQ.2.1,vP.2.2.2,cp,sign]
    exact ContinuousAnchorSupport.impossible V W cn sign ha (shape.trans same)
      lowerV vQ vR S T wall cut actualApart

#print axioms point
end N12Compact.Completion.OtherCases.C1089.ContinuousAnchorCenter
