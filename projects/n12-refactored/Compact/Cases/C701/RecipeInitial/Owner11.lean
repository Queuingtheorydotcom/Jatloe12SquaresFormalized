import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch00
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch01
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch02
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch03
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch04
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch05
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch06
import Compact.Cases.C701.RecipeInitial.Batches.Owner11Batch07
import Compact.Preservation.C701

namespace N12Compact.C701RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries11 : List (DirectRecipeTable.Entry bank inside11 outside11) :=
  entries11_0 ++
  entries11_1 ++
  entries11_2 ++
  entries11_3 ++
  entries11_4 ++
  entries11_5 ++
  entries11_6 ++
  entries11_7

theorem entries11_checked : ∀ entry ∈ entries11, entry.Check := by
  unfold entries11
  simp only [List.forall_mem_append]
  exact ⟨entries11_0_checked, entries11_1_checked, entries11_2_checked, entries11_3_checked, entries11_4_checked, entries11_5_checked, entries11_6_checked, entries11_7_checked⟩

def owner11 : Owner :=
  DirectRecipeTable.checkedOwner bank inside11 outside11 entries11 entries11_checked

theorem owner11_checked : owner11.Check :=
  DirectRecipeTable.checkedOwner_check bank inside11 outside11
    entries11 entries11_checked angles64_cover_kernel

theorem owner11_leaves_shared :
    owner11.leaves = Preservation.C701.continuousScout701Domain11_0 := by
  unfold owner11
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C701RecipeInitial
