import Compact.Cases.C973.DirectPruning.Step22Batch00
import Compact.Cases.C973.DirectPruning.Step22Batch01
import Compact.Cases.C973.DirectPruning.Step22Batch02
import Compact.Cases.C973.DirectPruning.Step22Batch03
import Compact.Preservation.C973
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C973DirectPruning.Step22
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open N12Compact.Preservation.C973

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C973DirectPruning.Step22Batch00.plans ++ N12Compact.C973DirectPruning.Step22Batch01.plans ++ N12Compact.C973DirectPruning.Step22Batch02.plans ++ N12Compact.C973DirectPruning.Step22Batch03.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C973DirectPruning.Step22Batch00.plans_checked, N12Compact.C973DirectPruning.Step22Batch01.plans_checked, N12Compact.C973DirectPruning.Step22Batch02.plans_checked, N12Compact.C973DirectPruning.Step22Batch03.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout973Domain6_0Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout973Domain6_23Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout973Domain6_0Ids, continuousScout973Domain5_22Ids, continuousScout973Domain6_23Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout973Domain6_0 q)
    (neighbors : OrientedPoseCovered continuousScout973Domain5_22 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout973Domain6_23 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C973DirectPruning.Step22
