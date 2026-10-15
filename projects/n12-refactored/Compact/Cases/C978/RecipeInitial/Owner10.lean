import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch00
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch01
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch02
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch03
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch04
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch05
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch06
import Compact.Cases.C978.RecipeInitial.Batches.Owner10Batch07
import Compact.Preservation.C978

namespace N12Compact.C978RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries10 : List (DirectRecipeTable.Entry bank inside10 outside10) :=
  entries10_0 ++
  entries10_1 ++
  entries10_2 ++
  entries10_3 ++
  entries10_4 ++
  entries10_5 ++
  entries10_6 ++
  entries10_7

theorem entries10_checked : ∀ entry ∈ entries10, entry.Check := by
  unfold entries10
  simp only [List.forall_mem_append]
  exact ⟨entries10_0_checked, entries10_1_checked, entries10_2_checked, entries10_3_checked, entries10_4_checked, entries10_5_checked, entries10_6_checked, entries10_7_checked⟩

def owner10 : Owner :=
  DirectRecipeTable.checkedOwner bank inside10 outside10 entries10 entries10_checked

theorem owner10_checked : owner10.Check :=
  DirectRecipeTable.checkedOwner_check bank inside10 outside10
    entries10 entries10_checked angles64_cover_kernel

theorem owner10_leaves_shared :
    owner10.leaves = Preservation.C978.continuousScout978Domain10_0 := by
  unfold owner10
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C978RecipeInitial
