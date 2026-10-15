import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch00
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch01
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch02
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch03
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch04
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch05
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch06
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch07
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch08
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch09
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch10
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch11
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch12
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch13
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch14
import Compact.Cases.C713.RecipeInitial.Batches.Owner00Batch15

namespace N12Compact.C713RecipeInitial
open S12 S12Pilot DirectPoseCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def entries0 : List (DirectRecipeTable.Entry bank inside0 outside0) :=
  entries0_0 ++
  entries0_1 ++
  entries0_2 ++
  entries0_3 ++
  entries0_4 ++
  entries0_5 ++
  entries0_6 ++
  entries0_7 ++
  entries0_8 ++
  entries0_9 ++
  entries0_10 ++
  entries0_11 ++
  entries0_12 ++
  entries0_13 ++
  entries0_14 ++
  entries0_15

theorem entries0_checked : ∀ entry ∈ entries0, entry.Check := by
  unfold entries0
  simp only [List.forall_mem_append]
  exact ⟨entries0_0_checked, entries0_1_checked, entries0_2_checked, entries0_3_checked, entries0_4_checked, entries0_5_checked, entries0_6_checked, entries0_7_checked, entries0_8_checked, entries0_9_checked, entries0_10_checked, entries0_11_checked, entries0_12_checked, entries0_13_checked, entries0_14_checked, entries0_15_checked⟩

def owner0 : Owner :=
  DirectRecipeTable.checkedOwner bank inside0 outside0 entries0 entries0_checked

theorem owner0_checked : owner0.Check :=
  DirectRecipeTable.checkedOwner_check bank inside0 outside0
    entries0 entries0_checked C713Shared.angles128_cover_kernel

end
end N12Compact.C713RecipeInitial
