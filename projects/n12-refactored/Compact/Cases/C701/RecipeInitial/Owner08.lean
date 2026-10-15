import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch00
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch01
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch02
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch03
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch04
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch05
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch06
import Compact.Cases.C701.RecipeInitial.Batches.Owner08Batch07
import Compact.Preservation.C701

namespace N12Compact.C701RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries8 : List (DirectRecipeTable.Entry bank inside8 outside8) :=
  entries8_0 ++
  entries8_1 ++
  entries8_2 ++
  entries8_3 ++
  entries8_4 ++
  entries8_5 ++
  entries8_6 ++
  entries8_7

theorem entries8_checked : ∀ entry ∈ entries8, entry.Check := by
  unfold entries8
  simp only [List.forall_mem_append]
  exact ⟨entries8_0_checked, entries8_1_checked, entries8_2_checked, entries8_3_checked, entries8_4_checked, entries8_5_checked, entries8_6_checked, entries8_7_checked⟩

def owner8 : Owner :=
  DirectRecipeTable.checkedOwner bank inside8 outside8 entries8 entries8_checked

theorem owner8_checked : owner8.Check :=
  DirectRecipeTable.checkedOwner_check bank inside8 outside8
    entries8 entries8_checked angles64_cover_kernel

theorem owner8_leaves_shared :
    owner8.leaves = Preservation.C701.continuousScout701Domain8_0 := by
  unfold owner8
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C701RecipeInitial
