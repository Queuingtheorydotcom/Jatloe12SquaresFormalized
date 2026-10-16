import Compact.Cases.C701.DirectPruning.Step29Batch00
import Compact.Cases.C701.DirectPruning.Step29Batch01
import Compact.Cases.C701.DirectPruning.Step29Batch02
import Compact.Cases.C701.DirectPruning.Step29Batch03
import Compact.Preservation.C701
import Compact.Bridge.IndexedBlockedTarget

namespace N12Compact.C701DirectPruning.Step29
open S12 S12Pilot IntegerSupport C713Shared IndexedBlockedTarget
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open N12Compact.Preservation.C701

def plans : List (IndexedBlockedTarget.Plan HistoricalData.rowCount HistoricalData.poseCount) :=
  N12Compact.C701DirectPruning.Step29Batch00.plans ++ N12Compact.C701DirectPruning.Step29Batch01.plans ++ N12Compact.C701DirectPruning.Step29Batch02.plans ++ N12Compact.C701DirectPruning.Step29Batch03.plans

theorem plans_checked : ∀ plan ∈ plans, plan.Check dictionary := by
  unfold plans
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨N12Compact.C701DirectPruning.Step29Batch00.plans_checked, N12Compact.C701DirectPruning.Step29Batch01.plans_checked, N12Compact.C701DirectPruning.Step29Batch02.plans_checked, N12Compact.C701DirectPruning.Step29Batch03.plans_checked⟩

theorem source_ids : plans.map IndexedBlockedTarget.Plan.source = continuousScout701Domain3_29Ids := by
  decide +kernel

theorem targets_checked : IndexedBlockedTarget.TargetsIn plans continuousScout701Domain3_30Ids := by
  decide +kernel

def planHeaders : List (Fin HistoricalData.poseCount × Option (List (Fin HistoricalData.rowCount))) :=
  plans.map IndexedBlockedTarget.Plan.header

def stage : IndexedBlockedTarget.Stage dictionary :=
  ⟨continuousScout701Domain3_29Ids, continuousScout701Domain7_24Ids, continuousScout701Domain3_30Ids, plans⟩

theorem stage_checked : stage.Check := ⟨source_ids, targets_checked, plans_checked⟩

abbrev BlockOverlap : Prop := stage.BlockOverlap

theorem step_sound (overlap : BlockOverlap) (q t : OpenSquare)
    (incoming : OrientedPoseCovered continuousScout701Domain3_29 q)
    (neighbors : OrientedPoseCovered continuousScout701Domain7_24 t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered continuousScout701Domain3_30 q :=
  stage.step_sound HistoricalData.positive_denominators stage_checked overlap q t incoming neighbors disjoint

#print axioms step_sound
end
end N12Compact.C701DirectPruning.Step29
