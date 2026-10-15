import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch00
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch01
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch02
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch03
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch04
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch05
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch06
import Compact.Cases.C701.RecipeInitial.Batches.Owner04Batch07
import Compact.Preservation.C701

namespace N12Compact.C701RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries4 : List (DirectRecipeTable.Entry bank inside4 outside4) :=
  entries4_0 ++
  entries4_1 ++
  entries4_2 ++
  entries4_3 ++
  entries4_4 ++
  entries4_5 ++
  entries4_6 ++
  entries4_7

theorem entries4_checked : ∀ entry ∈ entries4, entry.Check := by
  unfold entries4
  simp only [List.forall_mem_append]
  exact ⟨entries4_0_checked, entries4_1_checked, entries4_2_checked, entries4_3_checked, entries4_4_checked, entries4_5_checked, entries4_6_checked, entries4_7_checked⟩

def owner4 : Owner :=
  DirectRecipeTable.checkedOwner bank inside4 outside4 entries4 entries4_checked

theorem owner4_checked : owner4.Check :=
  DirectRecipeTable.checkedOwner_check bank inside4 outside4
    entries4 entries4_checked angles64_cover_kernel

theorem owner4_leaves_shared :
    owner4.leaves = Preservation.C701.continuousScout701Domain4_0 := by
  unfold owner4
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C701RecipeInitial
