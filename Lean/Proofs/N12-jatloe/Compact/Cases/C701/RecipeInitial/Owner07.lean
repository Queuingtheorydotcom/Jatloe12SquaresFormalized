import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch00
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch01
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch02
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch03
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch04
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch05
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch06
import Compact.Cases.C701.RecipeInitial.Batches.Owner07Batch07
import Compact.Preservation.C701

namespace N12Compact.C701RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries7 : List (DirectRecipeTable.Entry bank inside7 outside7) :=
  entries7_0 ++
  entries7_1 ++
  entries7_2 ++
  entries7_3 ++
  entries7_4 ++
  entries7_5 ++
  entries7_6 ++
  entries7_7

theorem entries7_checked : ∀ entry ∈ entries7, entry.Check := by
  unfold entries7
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries7_0_checked, entries7_1_checked, entries7_2_checked, entries7_3_checked, entries7_4_checked, entries7_5_checked, entries7_6_checked, entries7_7_checked⟩

def owner7 : Owner :=
  DirectRecipeTable.checkedOwner bank inside7 outside7 entries7 entries7_checked

theorem owner7_checked : owner7.Check :=
  DirectRecipeTable.checkedOwner_check bank inside7 outside7
    entries7 entries7_checked angles64_cover_kernel

theorem owner7_leaves_shared :
    owner7.leaves = Preservation.C701.continuousScout701Domain7_0 := by
  unfold owner7
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C701RecipeInitial
