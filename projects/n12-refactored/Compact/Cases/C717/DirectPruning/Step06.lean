import Compact.Cases.C717.DirectPruning.Step06Batch00
import Compact.Cases.C717.DirectPruning.Step06Batch01
import Compact.Cases.C717.DirectPruning.Step06Batch02
import Compact.Cases.C717.DirectPruning.Step06Batch03
import Compact.Cases.C717.DirectPruning.Step06Batch04
import Compact.Cases.C717.DirectPruning.Step06Batch05
import Compact.Cases.C717.DirectPruning.Step06Batch06
import Compact.Cases.C717.DirectPruning.Step06Batch07
import Compact.Preservation.C717
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C717DirectPruning.Step06
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open N12Compact.Preservation.C717

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C717DirectPruning.Step06Batch00.plans ++ N12Compact.C717DirectPruning.Step06Batch01.plans ++ N12Compact.C717DirectPruning.Step06Batch02.plans ++ N12Compact.C717DirectPruning.Step06Batch03.plans ++ N12Compact.C717DirectPruning.Step06Batch04.plans ++ N12Compact.C717DirectPruning.Step06Batch05.plans ++ N12Compact.C717DirectPruning.Step06Batch06.plans ++ N12Compact.C717DirectPruning.Step06Batch07.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C717DirectPruning.Step06Batch00.plans_checked, N12Compact.C717DirectPruning.Step06Batch01.plans_checked, N12Compact.C717DirectPruning.Step06Batch02.plans_checked, N12Compact.C717DirectPruning.Step06Batch03.plans_checked, N12Compact.C717DirectPruning.Step06Batch04.plans_checked, N12Compact.C717DirectPruning.Step06Batch05.plans_checked, N12Compact.C717DirectPruning.Step06Batch06.plans_checked, N12Compact.C717DirectPruning.Step06Batch07.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout717Domain6_6Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout717Domain6_7Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout717Domain6_6Ids, continuousScout717Domain7_0Ids, continuousScout717Domain6_7Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout717Domain6_6 q)
    (neighbors : OrientedPoseCovered continuousScout717Domain7_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout717Domain6_7 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C717DirectPruning.Step06
