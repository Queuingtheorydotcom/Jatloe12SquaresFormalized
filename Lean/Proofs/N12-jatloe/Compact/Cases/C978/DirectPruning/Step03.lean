import Compact.Cases.C978.DirectPruning.Step03Batch00
import Compact.Cases.C978.DirectPruning.Step03Batch01
import Compact.Cases.C978.DirectPruning.Step03Batch02
import Compact.Cases.C978.DirectPruning.Step03Batch03
import Compact.Preservation.C978
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C978DirectPruning.Step03
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open N12Compact.Preservation.C978

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C978DirectPruning.Step03Batch00.plans ++ N12Compact.C978DirectPruning.Step03Batch01.plans ++ N12Compact.C978DirectPruning.Step03Batch02.plans ++ N12Compact.C978DirectPruning.Step03Batch03.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C978DirectPruning.Step03Batch00.plans_checked, N12Compact.C978DirectPruning.Step03Batch01.plans_checked, N12Compact.C978DirectPruning.Step03Batch02.plans_checked, N12Compact.C978DirectPruning.Step03Batch03.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout978Domain8_0Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout978Domain8_4Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout978Domain8_0Ids, continuousScout978Domain7_3Ids, continuousScout978Domain8_4Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout978Domain8_0 q)
    (neighbors : OrientedPoseCovered continuousScout978Domain7_3 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout978Domain8_4 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C978DirectPruning.Step03
