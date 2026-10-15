import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch00
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch01
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch02
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch03
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch04
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch05
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch06
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch07
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch08
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch09
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch10
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch11
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch12
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch13
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch14
import Compact.Cases.C717.RecipeInitial.Batches.Owner01Batch15
import Compact.Preservation.C717

namespace N12Compact.C717RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries1 : List (DirectRecipeTable.Entry bank inside1 outside1) :=
  entries1_0 ++
  entries1_1 ++
  entries1_2 ++
  entries1_3 ++
  entries1_4 ++
  entries1_5 ++
  entries1_6 ++
  entries1_7 ++
  entries1_8 ++
  entries1_9 ++
  entries1_10 ++
  entries1_11 ++
  entries1_12 ++
  entries1_13 ++
  entries1_14 ++
  entries1_15

theorem entries1_checked : ∀ entry ∈ entries1, entry.Check := by
  unfold entries1
  simp only [List.forall_mem_append]
  exact ⟨entries1_0_checked, entries1_1_checked, entries1_2_checked, entries1_3_checked, entries1_4_checked, entries1_5_checked, entries1_6_checked, entries1_7_checked, entries1_8_checked, entries1_9_checked, entries1_10_checked, entries1_11_checked, entries1_12_checked, entries1_13_checked, entries1_14_checked, entries1_15_checked⟩

def owner1 : Owner :=
  DirectRecipeTable.checkedOwner bank inside1 outside1 entries1 entries1_checked

theorem owner1_checked : owner1.Check :=
  DirectRecipeTable.checkedOwner_check bank inside1 outside1
    entries1 entries1_checked angles128_cover_kernel

theorem owner1_leaves_shared :
    owner1.leaves = Preservation.C717.continuousScout717Domain1_0 := by
  unfold owner1
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C717RecipeInitial
