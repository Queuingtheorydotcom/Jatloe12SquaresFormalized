import Compact.Completion.OtherCases.MergedPending.UpperCenters
import Compact.Cases.C868.UpperNonnegative

/-! The completed two-square nonnegative-upper ending transfers to the
three pending merged families. Both foreign top points retain their real
owners. The result is a strict signed canonical frame for the SAME merged
square, not a whole-family exclusion. Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot C977CornerCubic CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem UpperData.nonnegative_upper_impossible {A H O L : OpenSquare}
    (h : UpperData A H O L) (ac : 0<A.c) (canonical : |A.s|≤A.c)
    (normalH : Normal H.c H.s) (center : H.Inside 2 2)
    (below : A.Inside 2 (3/2)) (missingTopRight : ¬H.Inside (113/50) 3) : False := by
  by_cases nonnegative : 0≤A.s
  · exact h.positive_impossible
      ⟨nonnegative,by simpa only [abs_of_nonneg nonnegative] using canonical,
        A.unit_normal⟩ normalH
  · have negative : A.s<0 := lt_of_not_ge nonnegative
    exact C868.UpperNonnegative.impossible A H
      ⟨⟨by linarith only [negative],
          by simpa only [abs_of_neg negative] using canonical,
          by nlinarith only [A.unit_normal]⟩,
        normalH,h.size,h.sameUpper,h.southwest,h.south,h.west,h.halfWest,below,
        h.northwest,h.northeast,center,
        (fun own => h.apartBottom _ _
          ⟨h.bottomBar _ (by norm_num) (by norm_num),own⟩),
        (fun own => h.apartLeft _ _
          ⟨own,h.leftBar _ (by norm_num) (by norm_num)⟩),
        h.missingTop,missingTopRight,h.apartUpper⟩

theorem upper_negative_frame (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k) :
    ∃ H : OpenSquare,0<H.c ∧ H.s<0 ∧ -H.s≤H.c ∧
      H.side=(owner p 3072).side ∧
      (∀ x y,H.Inside x y↔(owner p 3072).Inside x y) := by
  obtain ⟨A,ac,ca,sa,ia,_⟩ := ClosedFrames.canonical_frame (owner p 256)
  obtain ⟨H,hc,ch,sh,ih,_⟩ := ClosedFrames.canonical_frame (owner p 3072)
  have negative : H.s<0 := by
    apply lt_of_not_ge
    intro nonnegative
    have hcOrder : H.s≤H.c := by simpa only [abs_of_nonneg nonnegative] using ch
    have center := upper_nonnegative_center k p hf member H hc nonnegative hcOrder sh ih
    apply ((upper_data k p hf member).reframe A H sa sh ia ih).nonnegative_upper_impossible
      ac ca ⟨nonnegative,hcOrder,H.unit_normal⟩ center
      ((ia _ _).mpr (southwest_crosspoints k p hf).1)
    exact fun own => apart _ p hf 3072 16 member (common_member k 16 (by decide))
      (by decide) _ _ ⟨(ih _ _).mp own,(walls k p hf).topSingleton _ le_rfl (by norm_num)⟩
  exact ⟨H,hc,negative,by simpa only [abs_of_neg negative] using ch,sh,ih⟩

theorem c700_transposed_negative_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    ∃ H : OpenSquare,0<H.c ∧ H.s<0 ∧ -H.s≤H.c ∧
      H.side=(owner p 1536).side ∧
      (∀ x y,H.Inside x y↔(owner p 1536).Inside y x) := by
  obtain ⟨A,ac,ca,sa,ia,_⟩ := ClosedFrames.canonical_frame (pullSwap (owner p 256))
  obtain ⟨H,hc,ch,sh,ih,_⟩ := ClosedFrames.canonical_frame (pullSwap (owner p 1536))
  have original (x y : ℝ) : H.Inside x y↔(owner p 1536).Inside y x :=
    (ih x y).trans (inside_pullSwap _ _ _)
  have negative : H.s<0 := by
    apply lt_of_not_ge
    intro nonnegative
    have hcOrder : H.s≤H.c := by simpa only [abs_of_nonneg nonnegative] using ch
    have center := c700_transposed_nonnegative_center p hf H hc nonnegative hcOrder sh original
    apply ((c700_transposed_data p hf).reframe A H sa sh ia ih).nonnegative_upper_impossible
      ac ca ⟨nonnegative,hcOrder,H.unit_normal⟩ center
      ((ia _ _).mpr ((inside_pullSwap _ _ _).mpr (southwest_crosspoints .c700 p hf).2))
    exact fun own => apart _ p hf 1536 32 (by decide +kernel) (by decide +kernel)
      (by decide) _ _ ⟨(original _ _).mp own,c700_right_singleton p hf _ le_rfl (by norm_num)⟩
  exact ⟨H,hc,negative,by simpa only [abs_of_neg negative] using ch,sh,original⟩

/-- Translate the preceding signed chart back to the original physical
coordinates. C700's actual merged1536 has a strictly positive canonical
frame; its original upper/lower markers have not been interchanged. -/
theorem c700_positive_merged_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    ∃ H : OpenSquare,0<H.c ∧ 0<H.s ∧ H.s≤H.c ∧
      H.side=(owner p 1536).side ∧
      (∀ x y,H.Inside x y↔(owner p 1536).Inside x y) := by
  obtain ⟨q,cp,negative,canonical,shape,inside⟩ := c700_transposed_negative_frame p hf
  let H := turnFrame (turnFrame (turnFrame (pullSwap q)))
  have hc : H.c=q.c := by simp only [H,turnFrame,pullSwap,neg_neg]
  have hs : H.s= -q.s := by simp only [H,turnFrame,pullSwap,neg_neg]
  refine ⟨H,by simpa only [hc] using cp,?_,?_,shape,?_⟩
  · rw [hs]; linarith only [negative]
  · simpa only [hc,hs] using canonical
  · intro x y
    simp only [H,turnFrame_inside,inside_pullSwap]
    exact inside y x

end
#print axioms upper_negative_frame
#print axioms c700_positive_merged_frame
end N12Compact.MergedPending
