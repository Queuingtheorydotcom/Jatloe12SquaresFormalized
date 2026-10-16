import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch00
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch01
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch02
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch03
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch04
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch05
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch06
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch07
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch08
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch09
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch10
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch11
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch12
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch13
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch14
import Compact.Cases.C979.RecipeInitial.Batches.Owner05Batch15
import Compact.Preservation.C979

namespace N12Compact.C979RecipeInitial
open S12 S12Pilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

open DirectPoseCover Preservation.InitialBank

def entries5 : List (DirectRecipeTable.Entry bank inside5 outside5) :=
  entries5_0 ++
  entries5_1 ++
  entries5_2 ++
  entries5_3 ++
  entries5_4 ++
  entries5_5 ++
  entries5_6 ++
  entries5_7 ++
  entries5_8 ++
  entries5_9 ++
  entries5_10 ++
  entries5_11 ++
  entries5_12 ++
  entries5_13 ++
  entries5_14 ++
  entries5_15

theorem entries5_checked : ∀ entry ∈ entries5, entry.Check := by
  unfold entries5
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries5_0_checked, entries5_1_checked, entries5_2_checked, entries5_3_checked, entries5_4_checked, entries5_5_checked, entries5_6_checked, entries5_7_checked, entries5_8_checked, entries5_9_checked, entries5_10_checked, entries5_11_checked, entries5_12_checked, entries5_13_checked, entries5_14_checked, entries5_15_checked⟩

def owner5 : Owner :=
  DirectRecipeTable.checkedOwner bank inside5 outside5 entries5 entries5_checked

theorem owner5_checked : owner5.Check :=
  DirectRecipeTable.checkedOwner_check bank inside5 outside5
    entries5 entries5_checked angles128_cover_kernel

theorem owner5_leaves_shared :
    owner5.leaves = Preservation.C979.continuousScout979Domain5_0 := by
  unfold owner5
  rw [DirectRecipeTable.checkedOwner_leaves]
  rfl

end
end N12Compact.C979RecipeInitial
