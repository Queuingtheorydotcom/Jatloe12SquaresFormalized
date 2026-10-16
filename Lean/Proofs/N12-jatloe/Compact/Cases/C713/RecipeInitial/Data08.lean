import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch00
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch01
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch02
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch03
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch04
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch05
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch06
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch07
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch08
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch09
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch10
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch11
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch12
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch13
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch14
import Compact.Cases.C713.RecipeInitial.Batches.Owner08Batch15

namespace N12Compact.C713RecipeInitial
open S12 S12Pilot DirectPoseCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def entries8 : List (DirectRecipeTable.Entry bank inside8 outside8) :=
  entries8_0 ++
  entries8_1 ++
  entries8_2 ++
  entries8_3 ++
  entries8_4 ++
  entries8_5 ++
  entries8_6 ++
  entries8_7 ++
  entries8_8 ++
  entries8_9 ++
  entries8_10 ++
  entries8_11 ++
  entries8_12 ++
  entries8_13 ++
  entries8_14 ++
  entries8_15

theorem entries8_checked : ∀ entry ∈ entries8, entry.Check := by
  unfold entries8
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries8_0_checked, entries8_1_checked, entries8_2_checked, entries8_3_checked, entries8_4_checked, entries8_5_checked, entries8_6_checked, entries8_7_checked, entries8_8_checked, entries8_9_checked, entries8_10_checked, entries8_11_checked, entries8_12_checked, entries8_13_checked, entries8_14_checked, entries8_15_checked⟩

def owner8 : Owner :=
  DirectRecipeTable.checkedOwner bank inside8 outside8 entries8 entries8_checked

theorem owner8_checked : owner8.Check :=
  DirectRecipeTable.checkedOwner_check bank inside8 outside8
    entries8 entries8_checked C713Shared.angles128_cover_kernel

end
end N12Compact.C713RecipeInitial
