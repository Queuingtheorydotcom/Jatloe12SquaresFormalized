import Compact.Completion.CommonCases.SingletonMissing
import Compact.Completion.OtherCases.C983.C974LocalEnding
import Compact.Completion.OtherCases.C983.F4MergedCenterEnding

/-! Actual F4 corner-root entrance. The compact missing-corner singleton
proof now supplies the two stronger seeds that the original local adapters
retained explicitly. The merged 2304 owner remains one physical square.
Source composition only; no compiler acceptance is asserted. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f4_left_singleton_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    (owners p 1).Inside 1 1 := by
  by_contra missing
  have exactMarkers : ExactMarkers (owners p 1) {1} := by
    convert owners_markers p hf 1 using 1 <;> decide +kernel
  have seeds := CommonCases.SingletonMissing.one_missing_points (owners p 1)
    (owners_side p 1) (owners_cap p 1) (owners_contained p 1) exactMarkers missing
  exact C974LocalEnding.left_missing_corner_excluded_of_seeds p hf f4 missing
    seeds.1 seeds.2

theorem f4_bottom_singleton_seeds (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    ¬(owners p 0).Inside 1 1 ∧ (owners p 0).Inside (91/50) 1 ∧
      (owners p 0).Inside (49/25) (19/25) := by
  have missing : ¬(owners p 0).Inside 1 1 := fun own =>
    owners_apart p hf 0 1 (by decide +kernel) _ _
      ⟨own,f4_left_singleton_corner p hf f4⟩
  have exactMarkers : ExactMarkers (owners p 0) {0} := by
    convert owners_markers p hf 0 using 1 <;> decide +kernel
  exact ⟨missing,CommonCases.SingletonMissing.zero_missing_points (owners p 0)
    (owners_side p 0) (owners_cap p 0) (owners_contained p 0) exactMarkers missing⟩

theorem f4_merged_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    (owners p 7).Inside 2 2 :=
  F4MergedCenter.center_of_singleton_corner p hf f4
    (f4_left_singleton_corner p hf f4)

end
#print axioms f4_left_singleton_corner
#print axioms f4_bottom_singleton_seeds
#print axioms f4_merged_center
end N12Compact.Completion.OtherCases.C983
