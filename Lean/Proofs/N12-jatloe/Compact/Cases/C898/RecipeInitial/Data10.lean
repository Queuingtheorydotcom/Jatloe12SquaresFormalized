import Compact.Cases.C898.RecipeInitial.Batch10_00
import Compact.Cases.C898.RecipeInitial.Batch10_01
import Compact.Cases.C898.RecipeInitial.Batch10_02
import Compact.Cases.C898.RecipeInitial.Batch10_03
import Compact.Cases.C898.RecipeInitial.Batch10_04
import Compact.Cases.C898.RecipeInitial.Batch10_05
import Compact.Cases.C898.RecipeInitial.Batch10_06
import Compact.Cases.C898.RecipeInitial.Batch10_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries10 : List (DirectRecipeTable.Entry bank inside10 outside10) :=
  entries10_0 ++
  entries10_1 ++
  entries10_2 ++
  entries10_3 ++
  entries10_4 ++
  entries10_5 ++
  entries10_6 ++
  entries10_7

theorem entries10_checked : ∀ entry ∈ entries10, entry.Check := by
  unfold entries10
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries10_0_checked, entries10_1_checked, entries10_2_checked, entries10_3_checked, entries10_4_checked, entries10_5_checked, entries10_6_checked, entries10_7_checked⟩

noncomputable def owner10 : Owner :=
  DirectRecipeTable.checkedOwner bank inside10 outside10 entries10 entries10_checked

theorem owner10_checked : owner10.Check :=
  DirectRecipeTable.checkedOwner_check bank inside10 outside10
    entries10 entries10_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
