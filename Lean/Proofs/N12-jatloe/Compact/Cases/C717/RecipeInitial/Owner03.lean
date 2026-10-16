import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch00
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch01
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch02
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch03
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch04
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch05
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch06
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch07
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch08
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch09
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch10
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch11
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch12
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch13
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch14
import Compact.Cases.C717.RecipeInitial.Batches.Owner03Batch15
import Compact.Preservation.C717

namespace N12Compact.C717RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries3 : List (DirectRecipeTable.Entry bank inside3 outside3) :=
  entries3_0 ++
  entries3_1 ++
  entries3_2 ++
  entries3_3 ++
  entries3_4 ++
  entries3_5 ++
  entries3_6 ++
  entries3_7 ++
  entries3_8 ++
  entries3_9 ++
  entries3_10 ++
  entries3_11 ++
  entries3_12 ++
  entries3_13 ++
  entries3_14 ++
  entries3_15

theorem entries3_checked : ∀ entry ∈ entries3, entry.Check := by
  unfold entries3
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries3_0_checked, entries3_1_checked, entries3_2_checked, entries3_3_checked, entries3_4_checked, entries3_5_checked, entries3_6_checked, entries3_7_checked, entries3_8_checked, entries3_9_checked, entries3_10_checked, entries3_11_checked, entries3_12_checked, entries3_13_checked, entries3_14_checked, entries3_15_checked⟩

def owner3 : Owner :=
  DirectRecipeTable.checkedOwner bank inside3 outside3 entries3 entries3_checked

theorem owner3_checked : owner3.Check :=
  DirectRecipeTable.checkedOwner_check bank inside3 outside3
    entries3 entries3_checked angles128_cover_kernel

theorem owner3_leaves_shared :
    owner3.leaves = Preservation.C717.continuousScout717Domain3_0 := by
  unfold owner3
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C717RecipeInitial
