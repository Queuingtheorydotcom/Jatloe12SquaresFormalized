import Compact.Completion.OtherCases.MergedPending.CentralPoints
import Compact.Completion.OtherCases.MergedPending.UpperSectorCore

/-! Original-owner entrances to the upper-merged local reduction. C683 and
C867 use their actual merged3072 directly. C700 uses a literal transpose
of its actual merged1536, SW256 and foreign singleton/wall owners. This
does not identify any two packing owners or assert a family symmetry.
The exported conclusions retain the unproved orientation sectors. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem upper_data (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k) :
    UpperData (owner p 256) (owner p 3072) (owner p 1) (owner p 2) := by
  have shape (m : Nat) : (owner p m).side=p.commonSide := p.congruent _
  have points := southwest_points k p hf
  have half := southwest_crosspoints k p hf
  have marks := upper_merged_markers k p hf member
  have w := walls k p hf
  have marker := seed _ p hf 256 (common_member k 256 (by decide))
    (33/20,33/20) (by decide +kernel)
  have bottomMarker := seed _ p hf 1 (common_member k 1 (by decide))
    (1,457/500) (by decide +kernel)
  have bottomOffrow := seed _ p hf 1 (common_member k 1 (by decide))
    (187/100,19/25) (by decide +kernel)
  have bottomMissing := missing_marker _ p hf 1 (common_member k 1 (by decide))
    13 (by decide +kernel)
  have top := (auxiliary_exact p 32768 14 (by norm_num)).mpr
    (common_labels k p hf).top.2
  norm_num [S12.marker,auxPoints,fPoints,gPoints] at
    marker bottomMarker bottomOffrow bottomMissing top
  refine ⟨side p 256,(shape 256).trans (shape 3072).symm,
    (shape 1).trans (shape 256).symm,box p 1,marker,points.1,points.2.1,
    half.2,marks.1,marks.2,bottomMarker,bottomOffrow,
    w.bottomSingleton,w.leftSingleton,bottomMissing,?_,?_,?_,?_⟩
  · exact apart _ p hf 256 3072 (common_member k 256 (by decide)) member (by decide)
  · exact apart _ p hf 1 256 (common_member k 1 (by decide))
      (common_member k 256 (by decide)) (by decide)
  · exact apart _ p hf 256 2 (common_member k 256 (by decide))
      (common_member k 2 (by decide)) (by decide)
  · exact fun own => apart _ p hf 3072 32768 member
      (common_member k 32768 (by decide)) (by decide) _ _ ⟨own,top⟩

theorem upper_remaining (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k) :
    UpperResidue (owner p 256) (owner p 3072) (owner p 1) :=
  (upper_data k p hf member).remaining

/-- C700's whole geometric input is transposed, including both different
singleton bars. The actual upper-left marker remains outside merged1536;
no extra marker from C702 is supplied to the left wall. -/
theorem c700_transposed_data (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    UpperData (pullSwap (owner p 256)) (pullSwap (owner p 1536))
      (pullSwap (owner p 2)) (pullSwap (owner p 1)) := by
  have shape (m : Nat) : (owner p m).side=p.commonSide := p.congruent _
  have points := southwest_points .c700 p hf
  have half := southwest_crosspoints .c700 p hf
  have marks := c700_merged_markers p hf
  have w := walls .c700 p hf
  have marker := seed _ p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
  have bottomMarker := seed _ p hf 2 (by decide +kernel) (457/500,1) (by decide +kernel)
  have bottomOffrow := seed _ p hf 2 (by decide +kernel)
    (19/25,187/100) (by decide +kernel)
  have bottomMissing := missing_marker _ p hf 2 (by decide +kernel) 12 (by decide +kernel)
  have right := (auxiliary_exact p 16384 8 (by norm_num)).mpr (c700_right_labels p hf).1
  norm_num [S12.marker,auxPoints,fPoints,gPoints] at
    marker bottomMarker bottomOffrow bottomMissing right
  refine ⟨side p 256,(shape 256).trans (shape 1536).symm,
    (shape 2).trans (shape 256).symm,container_pullSwap _ (box p 2),
    (inside_pullSwap _ _ _).mpr marker,(inside_pullSwap _ _ _).mpr points.2.1,
    (inside_pullSwap _ _ _).mpr points.1,(inside_pullSwap _ _ _).mpr half.1,
    (inside_pullSwap _ _ _).mpr marks.1,(inside_pullSwap _ _ _).mpr marks.2,
    (inside_pullSwap _ _ _).mpr bottomMarker,(inside_pullSwap _ _ _).mpr bottomOffrow,
    ?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun x low high => (inside_pullSwap _ _ _).mpr (w.leftSingleton x low high)
  · exact fun y low high => (inside_pullSwap _ _ _).mpr (w.bottomSingleton y low high)
  · exact fun own => bottomMissing ((inside_pullSwap _ _ _).mp own)
  · intro x y points
    exact apart _ p hf 256 1536 (by decide +kernel) (by decide +kernel) (by decide)
      y x ⟨(inside_pullSwap _ _ _).mp points.1,(inside_pullSwap _ _ _).mp points.2⟩
  · intro x y points
    exact apart _ p hf 2 256 (by decide +kernel) (by decide +kernel) (by decide)
      y x ⟨(inside_pullSwap _ _ _).mp points.1,(inside_pullSwap _ _ _).mp points.2⟩
  · intro x y points
    exact apart _ p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide)
      y x ⟨(inside_pullSwap _ _ _).mp points.1,(inside_pullSwap _ _ _).mp points.2⟩
  · exact fun own => apart _ p hf 1536 16384 (by decide +kernel)
      (by decide +kernel) (by decide) _ _ ⟨(inside_pullSwap _ _ _).mp own,right⟩

theorem c700_remaining (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    UpperResidue (pullSwap (owner p 256)) (pullSwap (owner p 1536))
      (pullSwap (owner p 2)) :=
  (c700_transposed_data p hf).remaining

end
#print axioms upper_remaining
#print axioms c700_remaining
end N12Compact.MergedPending
