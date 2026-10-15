import Compact.Cases.C979.DirectPruning.Step04Batch00
import Compact.Cases.C979.DirectPruning.Step04Batch01
import Compact.Cases.C979.DirectPruning.Step04Batch02
import Compact.Cases.C979.DirectPruning.Step04Batch03
import Compact.Cases.C979.DirectPruning.Step04Batch04
import Compact.Cases.C979.DirectPruning.Step04Batch05
import Compact.Cases.C979.DirectPruning.Step04Batch06
import Compact.Cases.C979.DirectPruning.Step04Batch07
import Compact.Preservation.C979
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C979DirectPruning.Step04
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open N12Compact.Preservation.C979

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C979DirectPruning.Step04Batch00.plans ++ N12Compact.C979DirectPruning.Step04Batch01.plans ++ N12Compact.C979DirectPruning.Step04Batch02.plans ++ N12Compact.C979DirectPruning.Step04Batch03.plans ++ N12Compact.C979DirectPruning.Step04Batch04.plans ++ N12Compact.C979DirectPruning.Step04Batch05.plans ++ N12Compact.C979DirectPruning.Step04Batch06.plans ++ N12Compact.C979DirectPruning.Step04Batch07.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C979DirectPruning.Step04Batch00.plans_checked, N12Compact.C979DirectPruning.Step04Batch01.plans_checked, N12Compact.C979DirectPruning.Step04Batch02.plans_checked, N12Compact.C979DirectPruning.Step04Batch03.plans_checked, N12Compact.C979DirectPruning.Step04Batch04.plans_checked, N12Compact.C979DirectPruning.Step04Batch05.plans_checked, N12Compact.C979DirectPruning.Step04Batch06.plans_checked, N12Compact.C979DirectPruning.Step04Batch07.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout979Domain7_0Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout979Domain7_5Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout979Domain7_0Ids, continuousScout979Domain5_0Ids, continuousScout979Domain7_5Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout979Domain7_0 q)
    (neighbors : OrientedPoseCovered continuousScout979Domain5_0 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout979Domain7_5 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C979DirectPruning.Step04
