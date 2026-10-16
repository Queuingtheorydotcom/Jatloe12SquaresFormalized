import Compact.Cases.C717.DirectPruning.Step10Batch00
import Compact.Cases.C717.DirectPruning.Step10Batch01
import Compact.Preservation.C717
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C717DirectPruning.Step10
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open N12Compact.Preservation.C717

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C717DirectPruning.Step10Batch00.plans ++ N12Compact.C717DirectPruning.Step10Batch01.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C717DirectPruning.Step10Batch00.plans_checked, N12Compact.C717DirectPruning.Step10Batch01.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout717Domain7_10Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout717Domain7_11Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout717Domain7_10Ids, continuousScout717Domain11_0Ids, continuousScout717Domain7_11Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout717Domain7_10 q)
    (neighbors : OrientedPoseCovered continuousScout717Domain11_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout717Domain7_11 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C717DirectPruning.Step10
