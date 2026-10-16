import Compact.Core.RelaxationHints
import Compact.Bridge.IndexedRelaxation

/-! Relaxations whose only independent source data are two original pose IDs.

The local rows and small witnesses are caches, not additional assumptions:
row equality proofs bind them to the original dictionary and the numeric
checker independently verifies every target. No proof replays witness search.
-/

namespace N12Compact.RelaxationTable
open IntegerSupport IndexedRelaxation S12 S12Pilot

structure Spec (poseCount : Nat) where
  source : Fin poseCount
  target : Fin poseCount
  deriving DecidableEq

structure Entry {rowCount poseCount angleCount : Nat}
    (dictionary : Dictionary rowCount poseCount angleCount) where
  spec : Spec poseCount
  inputs : List Row
  targets : List Row
  inputs_exact : inputs = (dictionary.poseRows spec.source).map dictionary.rows
  targets_exact : targets = (dictionary.poseRows spec.target).map dictionary.rows
  hints : List RelaxationHints.Hint

variable {rowCount poseCount angleCount : Nat}
variable {dictionary : Dictionary rowCount poseCount angleCount}

def Entry.Check (entry : Entry dictionary) : Prop :=
  dictionary.poseAngle entry.spec.source = dictionary.poseAngle entry.spec.target ∧
  RelaxationHints.Check entry.inputs entry.targets entry.hints

instance (entry : Entry dictionary) : Decidable entry.Check :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Entry.sound (entry : Entry dictionary) (checked : entry.Check)
    (positive : ∀ r, 0 < dictionary.denominators r) (q : OpenSquare)
    (holds : (dictionary.pose entry.spec.source).OrientedRealizes q) :
    (dictionary.pose entry.spec.target).OrientedRealizes q := by
  have inputs_hold : ∀ row ∈ entry.inputs, row.Holds ![centerX q, centerY q] := by
    intro row row_member
    rw [entry.inputs_exact] at row_member
    obtain ⟨index, index_member, rfl⟩ := List.mem_map.mp row_member
    apply ((dictionary.rows index).normalized_holds_iff _ (positive index) _).mp
    exact holds.1.1 _ (List.mem_map.mpr ⟨index, index_member, rfl⟩)
  have targets_hold := RelaxationHints.sound checked.2 ![centerX q, centerY q] inputs_hold
  apply dictionary.transfer checked.1 positive q holds
  intro row member
  apply targets_hold (dictionary.rows row)
  rw [entry.targets_exact]
  exact List.mem_map.mpr ⟨row, member, rfl⟩

def CoverCheck (sources targets : List (Fin poseCount))
    (entries : List (Entry dictionary)) : Prop :=
  ∀ source ∈ sources, ∃ entry ∈ entries,
    entry.spec.source = source ∧ entry.spec.target ∈ targets

instance (sources targets : List (Fin poseCount)) (entries : List (Entry dictionary)) :
    Decidable (CoverCheck sources targets entries) := by
  unfold CoverCheck
  letI : DecidablePred (fun source => ∃ entry ∈ entries,
      entry.spec.source = source ∧ entry.spec.target ∈ targets) :=
    fun source => List.decidableBEx _ entries
  exact List.decidableBAll _ sources

theorem cover_sound (sources targets : List (Fin poseCount))
    (entries : List (Entry dictionary)) (covered : CoverCheck sources targets entries)
    (checked : ∀ entry ∈ entries, entry.Check)
    (positive : ∀ r, 0 < dictionary.denominators r)
    (q : OpenSquare) (holds : OrientedPoseCovered (sources.map dictionary.pose) q) :
    OrientedPoseCovered (targets.map dictionary.pose) q := by
  obtain ⟨pose, pose_member, pose_holds⟩ := holds
  obtain ⟨source, source_member, rfl⟩ := List.mem_map.mp pose_member
  obtain ⟨entry, entry_mem, same_source, target_mem⟩ := covered source source_member
  refine ⟨dictionary.pose entry.spec.target,
    List.mem_map.mpr ⟨entry.spec.target, target_mem, rfl⟩, ?_⟩
  apply entry.sound (checked entry entry_mem) positive q
  simpa only [same_source] using pose_holds

#print axioms Entry.sound
#print axioms cover_sound
end N12Compact.RelaxationTable
