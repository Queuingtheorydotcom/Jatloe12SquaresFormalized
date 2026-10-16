import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch00
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch01
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch02
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch03
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch04
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch05
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch06
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch07
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch08
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch09
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch10
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch11
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch12
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch13
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch14
import Compact.Cases.C717.RecipeInitial.Batches.Owner02Batch15
import Compact.Preservation.C717

namespace N12Compact.C717RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries2 : List (DirectRecipeTable.Entry bank inside2 outside2) :=
  entries2_0 ++
  entries2_1 ++
  entries2_2 ++
  entries2_3 ++
  entries2_4 ++
  entries2_5 ++
  entries2_6 ++
  entries2_7 ++
  entries2_8 ++
  entries2_9 ++
  entries2_10 ++
  entries2_11 ++
  entries2_12 ++
  entries2_13 ++
  entries2_14 ++
  entries2_15

theorem entries2_checked : ∀ entry ∈ entries2, entry.Check := by
  unfold entries2
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries2_0_checked, entries2_1_checked, entries2_2_checked, entries2_3_checked, entries2_4_checked, entries2_5_checked, entries2_6_checked, entries2_7_checked, entries2_8_checked, entries2_9_checked, entries2_10_checked, entries2_11_checked, entries2_12_checked, entries2_13_checked, entries2_14_checked, entries2_15_checked⟩

def owner2 : Owner :=
  DirectRecipeTable.checkedOwner bank inside2 outside2 entries2 entries2_checked

theorem owner2_checked : owner2.Check :=
  DirectRecipeTable.checkedOwner_check bank inside2 outside2
    entries2 entries2_checked angles128_cover_kernel

theorem owner2_leaves_shared :
    owner2.leaves = Preservation.C717.continuousScout717Domain2_0 := by
  unfold owner2
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C717RecipeInitial
