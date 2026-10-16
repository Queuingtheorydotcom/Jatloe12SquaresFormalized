import Compact.Completion.OtherCases.MergedPending.NegativeUpperOutward
import Compact.Cases.C868.UpperNegativeCapGeometry
import Compact.Assembly.RowIdentity

/-! Original C683 and C867 contracts.  Their complete negative merged
square reduction meets the same actual top square in both angle ranges.
C683 never acquires a right-wall owner.  The original families and row
indices are retained literally.  Source only; not compiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot S12Completion C977CornerCubic CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem upper_merged_impossible (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k) : False := by
  obtain ⟨H,cp,negative,order,shape,inside⟩ := upper_negative_frame k p hf member
  have normal : Normal H.c (-H.s) :=
    ⟨by linarith only [negative],order,by nlinarith only [H.unit_normal]⟩
  have input : C868.UpperNegativeCap.Data (H.translated 2 2) :=
    { toInput := upper_negative_input k p hf member H normal shape inside
      nearFloor := upper_near_lower k p hf member H normal inside
      topCap := upper_top_cap k p hf member H normal shape inside
      nearCap := (upper_southeast_caps k p hf member H normal shape inside).2.1 }
  obtain ⟨T,tc,ts,topShape,topInside,_⟩ := ClosedFrames.positive_frame (owner p 32768)
  have topMember := common_member k 32768 (by decide)
  apply C868.UpperNegativeCap.impossible (H.translated 2 2) (T.translated 2 2) input
  · change 1<T.side
    simpa only [topShape] using side p 32768
  · exact tc
  · exact ts
  · norm_num only [inside_translated_iff]
    exact (topInside _ _).mpr ((top_reach k p hf).2 (6/5) le_rfl (by norm_num))
  · norm_num only [inside_translated_iff]
    apply (topInside _ _).mpr
    simpa using seed _ p hf 32768 topMember (2,1543/500) (by decide +kernel)
  · intro x y own
    exact apart _ p hf 3072 32768 member topMember (by decide) (2+x) (2+y)
      ⟨(inside _ _).mp ((inside_translated_iff H 2 2 x y).mp own.1),
        (topInside _ _).mp ((inside_translated_iff T 2 2 x y).mp own.2)⟩

theorem family683_excluded : ExcludesFamily (family .c683) := by
  intro p hf
  exact upper_merged_impossible .c683 p hf (by decide +kernel)

theorem family867_excluded : ExcludesFamily (family .c867) := by
  intro p hf
  exact upper_merged_impossible .c867 p hf (by decide +kernel)

private theorem lookup683 :
    (N12Compact.RowIdentity.rowAt 364).originalId=683 ∧
      (N12Compact.RowIdentity.rowAt 364).groups=family .c683 := by decide +kernel

private theorem lookup867 :
    (N12Compact.RowIdentity.rowAt 454).originalId=867 ∧
      (N12Compact.RowIdentity.rowAt 454).groups=family .c867 := by decide +kernel

theorem row683_family : ∀ r∈retainedRows,r.originalId=683 → r.groups=family .c683 :=
  N12Compact.RowIdentity.family_at 364 683 (family .c683) lookup683

theorem row867_family : ∀ r∈retainedRows,r.originalId=867 → r.groups=family .c867 :=
  N12Compact.RowIdentity.family_at 454 867 (family .c867) lookup867

theorem case683_excluded : ExcludesCase 683 := by
  intro r member identity
  simpa only [row683_family r member identity] using family683_excluded

theorem case867_excluded : ExcludesCase 867 := by
  intro r member identity
  simpa only [row867_family r member identity] using family867_excluded

end
#print axioms upper_merged_impossible
#print axioms case683_excluded
#print axioms case867_excluded
end N12Compact.MergedPending
