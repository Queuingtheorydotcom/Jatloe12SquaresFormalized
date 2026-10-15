import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch00
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch01
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch02
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch03
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch04
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch05
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch06
import Compact.Cases.C978.RecipeInitial.Batches.Owner09Batch07
import Compact.Preservation.C978

namespace N12Compact.C978RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries9 : List (DirectRecipeTable.Entry bank inside9 outside9) :=
  entries9_0 ++
  entries9_1 ++
  entries9_2 ++
  entries9_3 ++
  entries9_4 ++
  entries9_5 ++
  entries9_6 ++
  entries9_7

theorem entries9_checked : ∀ entry ∈ entries9, entry.Check := by
  unfold entries9
  simp only [List.forall_mem_append]
  exact ⟨entries9_0_checked, entries9_1_checked, entries9_2_checked, entries9_3_checked, entries9_4_checked, entries9_5_checked, entries9_6_checked, entries9_7_checked⟩

def owner9 : Owner :=
  DirectRecipeTable.checkedOwner bank inside9 outside9 entries9 entries9_checked

theorem owner9_checked : owner9.Check :=
  DirectRecipeTable.checkedOwner_check bank inside9 outside9
    entries9 entries9_checked angles64_cover_kernel

theorem owner9_leaves_shared :
    owner9.leaves = Preservation.C978.continuousScout978Domain9_0 := by
  unfold owner9
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C978RecipeInitial
