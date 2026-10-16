import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch00
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch01
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch02
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch03
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch04
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch05
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch06
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch07
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch08
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch09
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch10
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch11
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch12
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch13
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch14
import Compact.Cases.C717.RecipeInitial.Batches.Owner07Batch15
import Compact.Preservation.C717

namespace N12Compact.C717RecipeInitial
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
  entries7_7 ++
  entries7_8 ++
  entries7_9 ++
  entries7_10 ++
  entries7_11 ++
  entries7_12 ++
  entries7_13 ++
  entries7_14 ++
  entries7_15

theorem entries7_checked : ∀ entry ∈ entries7, entry.Check := by
  unfold entries7
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries7_0_checked, entries7_1_checked, entries7_2_checked, entries7_3_checked, entries7_4_checked, entries7_5_checked, entries7_6_checked, entries7_7_checked, entries7_8_checked, entries7_9_checked, entries7_10_checked, entries7_11_checked, entries7_12_checked, entries7_13_checked, entries7_14_checked, entries7_15_checked⟩

def owner7 : Owner :=
  DirectRecipeTable.checkedOwner bank inside7 outside7 entries7 entries7_checked

theorem owner7_checked : owner7.Check :=
  DirectRecipeTable.checkedOwner_check bank inside7 outside7
    entries7 entries7_checked angles128_cover_kernel

theorem owner7_leaves_shared :
    owner7.leaves = Preservation.C717.continuousScout717Domain7_0 := by
  unfold owner7
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C717RecipeInitial
