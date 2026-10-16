import Compact.Completion.OtherCases.MergedPending.C700OppositeOrigins
import Compact.Completion.OtherCases.MergedPending.CentralPoints
import Compact.Completion.CommonCases.SingletonMissing
import Compact.Completion.OtherCases.C983.C974LocalEnding

/-! The actual left singleton must own the southwest corner in C700.
The three-square ending is used after a literal coordinate exchange of
singleton2, left4096 and paired192. The absent northwest central marker
is only an exclusion of left4096; no fictitious owner is introduced. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

/-- Literal input of the local missing-corner contradiction. The two
strong seeds are forced from the assumed omission in the next theorem. -/
theorem c700_left_missing_input (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700)
    (missing : ¬(owner p 2).Inside 1 1)
    (seedA : (owner p 2).Inside 1 (91/50))
    (seedS : (owner p 2).Inside (19/25) (49/25)) :
    Completion.OtherCases.C983.C974LocalData.Input
      ((pullSwap (owner p 2)).translated 1 1)
      ((pullSwap (owner p 4096)).translated 1 1)
      ((pullSwap (owner p 192)).translated 1 1) := by
  have markK := seed _ p hf 2 (by decide +kernel) (457/500,1) (by decide +kernel)
  have markW := seed _ p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
  have corner := seed _ p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
  have missingMarker := missing_marker _ p hf 4096 (by decide +kernel) 11 (by decide +kernel)
  norm_num [S12.marker] at markK markW corner missingMarker
  have far := (left_reach .c700 p hf).2 (14/5) (by norm_num) le_rfl
  have middle := (southwest_crosspoints .c700 p hf).2
  have outer := (top_reach .c700 p hf).2 (3/2) (by norm_num) (by norm_num)
  refine ⟨side p 2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (p.congruent _).trans (p.congruent _).symm
  · exact (p.congruent _).trans (p.congruent _).symm
  · intro x y own
    have original : (owner p 2).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := (box p 2 _ _ original).1
    linarith only [wall]
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact markK
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact seedA
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact seedS
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact missing
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact c700_left_origin p hf
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact markW
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact far
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact missingMarker
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => apart _ p hf 4096 256
      (by decide +kernel) (by decide +kernel) (by decide) _ _ ⟨own,middle⟩
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => apart _ p hf 4096 32768
      (by decide +kernel) (by decide +kernel) (by decide) _ _ ⟨own,outer⟩
  · intro x y own
    have original : (owner p 192).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using own
    have wall := box p 192 _ _ original
    constructor <;> linarith only [wall.2.2.2,wall.1]
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact corner
  · norm_num only [inside_translated_iff,inside_pullSwap]
    exact fun own => apart _ p hf 192 32768
      (by decide +kernel) (by decide +kernel) (by decide) _ _ ⟨own,outer⟩
  · intro x y both
    have first : (owner p 2).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owner p 4096).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact apart _ p hf 2 4096 (by decide +kernel) (by decide +kernel) (by decide)
      _ _ ⟨first,last⟩
  · intro x y both
    have first : (owner p 2).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owner p 192).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact apart _ p hf 2 192 (by decide +kernel) (by decide +kernel) (by decide)
      _ _ ⟨first,last⟩
  · intro x y both
    have first : (owner p 4096).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.1
    have last : (owner p 192).Inside (1+y) (1+x) := by
      simpa only [inside_translated_iff,inside_pullSwap] using both.2
    exact apart _ p hf 4096 192 (by decide +kernel) (by decide +kernel) (by decide)
      _ _ ⟨first,last⟩

/-- Actual singleton2, not a free local square, contains the corner.
The exact singleton signature supplies every foreign marker omission. -/
theorem c700_left_singleton_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 2).Inside 1 1 := by
  classical
  by_contra missing
  have exactMask : ExactMarkers (owner p 2) (maskSupport 2) := by
    have hc := code _ p hf 2 (by decide +kernel)
    simpa only [owner,hc] using coded_exact p (ownerIndex p 2)
  have exactSingleton : ExactMarkers (owner p 2) {1} := by
    have support : maskSupport 2=({1} : Finset Marker) := by decide +kernel
    simpa only [support] using exactMask
  have size : (owner p 2).side≤1001/1000 := by
    change (p.square (ownerIndex p 2)).side≤1001/1000
    rw [p.congruent]
    exact p.side_le
  have strong := CommonCases.SingletonMissing.one_missing_points
    (owner p 2) (side p 2) size (box p 2) exactSingleton missing
  exact Completion.OtherCases.C983.C974LocalEnding.impossible _ _ _
    (c700_left_missing_input p hf missing strong.1 strong.2)

end
#print axioms c700_left_missing_input
#print axioms c700_left_singleton_corner
end N12Compact.MergedPending
