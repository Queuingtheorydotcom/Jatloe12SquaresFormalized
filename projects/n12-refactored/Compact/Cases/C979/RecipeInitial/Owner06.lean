import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch00
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch01
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch02
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch03
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch04
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch05
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch06
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch07
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch08
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch09
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch10
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch11
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch12
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch13
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch14
import Compact.Cases.C979.RecipeInitial.Batches.Owner06Batch15
import Compact.Preservation.C979

namespace N12Compact.C979RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries6 : List (DirectRecipeTable.Entry bank inside6 outside6) :=
  entries6_0 ++
  entries6_1 ++
  entries6_2 ++
  entries6_3 ++
  entries6_4 ++
  entries6_5 ++
  entries6_6 ++
  entries6_7 ++
  entries6_8 ++
  entries6_9 ++
  entries6_10 ++
  entries6_11 ++
  entries6_12 ++
  entries6_13 ++
  entries6_14 ++
  entries6_15

theorem entries6_checked : ∀ entry ∈ entries6, entry.Check := by
  unfold entries6
  simp only [List.forall_mem_append]
  exact ⟨entries6_0_checked, entries6_1_checked, entries6_2_checked, entries6_3_checked, entries6_4_checked, entries6_5_checked, entries6_6_checked, entries6_7_checked, entries6_8_checked, entries6_9_checked, entries6_10_checked, entries6_11_checked, entries6_12_checked, entries6_13_checked, entries6_14_checked, entries6_15_checked⟩

def owner6 : Owner :=
  DirectRecipeTable.checkedOwner bank inside6 outside6 entries6 entries6_checked

theorem owner6_checked : owner6.Check :=
  DirectRecipeTable.checkedOwner_check bank inside6 outside6
    entries6 entries6_checked angles128_cover_kernel

theorem owner6_leaves_shared :
    owner6.leaves = Preservation.C979.continuousScout979Domain6_0 := by
  unfold owner6
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C979RecipeInitial
