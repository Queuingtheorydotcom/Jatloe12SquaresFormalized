import Compact.Cases.C898.RecipeInitial.Batch02_00
import Compact.Cases.C898.RecipeInitial.Batch02_01
import Compact.Cases.C898.RecipeInitial.Batch02_02
import Compact.Cases.C898.RecipeInitial.Batch02_03
import Compact.Cases.C898.RecipeInitial.Batch02_04
import Compact.Cases.C898.RecipeInitial.Batch02_05
import Compact.Cases.C898.RecipeInitial.Batch02_06
import Compact.Cases.C898.RecipeInitial.Batch02_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries2 : List (DirectRecipeTable.Entry bank inside2 outside2) :=
  entries2_0 ++
  entries2_1 ++
  entries2_2 ++
  entries2_3 ++
  entries2_4 ++
  entries2_5 ++
  entries2_6 ++
  entries2_7

theorem entries2_checked : ∀ entry ∈ entries2, entry.Check := by
  unfold entries2
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries2_0_checked, entries2_1_checked, entries2_2_checked, entries2_3_checked, entries2_4_checked, entries2_5_checked, entries2_6_checked, entries2_7_checked⟩

noncomputable def owner2 : Owner :=
  DirectRecipeTable.checkedOwner bank inside2 outside2 entries2 entries2_checked

theorem owner2_checked : owner2.Check :=
  DirectRecipeTable.checkedOwner_check bank inside2 outside2
    entries2 entries2_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
