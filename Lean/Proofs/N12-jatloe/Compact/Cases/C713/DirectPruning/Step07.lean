import Compact.Cases.C713.DirectPruning.Step07Batch00
import Compact.Cases.C713.DirectPruning.Step07Batch01
import Compact.Cases.C713.DirectPruning.Step07Batch02
import Compact.Cases.C713.DirectPruning.Step07Batch03
import Compact.Cases.C713.DirectPruning.Step07Batch04
import Compact.Cases.C713.DirectPruning.Step07Batch05
import Compact.Cases.C713.DirectPruning.Step07Batch06
import Compact.Cases.C713.SharedDomains
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C713DirectPruning.Step07
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C713DirectPruning.Step07Batch00.plans ++ N12Compact.C713DirectPruning.Step07Batch01.plans ++ N12Compact.C713DirectPruning.Step07Batch02.plans ++ N12Compact.C713DirectPruning.Step07Batch03.plans ++ N12Compact.C713DirectPruning.Step07Batch04.plans ++ N12Compact.C713DirectPruning.Step07Batch05.plans ++ N12Compact.C713DirectPruning.Step07Batch06.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C713DirectPruning.Step07Batch00.plans_checked, N12Compact.C713DirectPruning.Step07Batch01.plans_checked, N12Compact.C713DirectPruning.Step07Batch02.plans_checked, N12Compact.C713DirectPruning.Step07Batch03.plans_checked, N12Compact.C713DirectPruning.Step07Batch04.plans_checked, N12Compact.C713DirectPruning.Step07Batch05.plans_checked, N12Compact.C713DirectPruning.Step07Batch06.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout713Domain7_7Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout713Domain7_8Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout713Domain7_7Ids, continuousScout713Domain6_5Ids, continuousScout713Domain7_8Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout713Domain7_7 q)
    (neighbors : OrientedPoseCovered continuousScout713Domain6_5 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout713Domain7_8 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C713DirectPruning.Step07
