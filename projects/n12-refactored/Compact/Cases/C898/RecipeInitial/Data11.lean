import Compact.Cases.C898.RecipeInitial.Batch11_00
import Compact.Cases.C898.RecipeInitial.Batch11_01
import Compact.Cases.C898.RecipeInitial.Batch11_02
import Compact.Cases.C898.RecipeInitial.Batch11_03
import Compact.Cases.C898.RecipeInitial.Batch11_04
import Compact.Cases.C898.RecipeInitial.Batch11_05
import Compact.Cases.C898.RecipeInitial.Batch11_06
import Compact.Cases.C898.RecipeInitial.Batch11_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries11 : List (DirectRecipeTable.Entry bank inside11 outside11) :=
  entries11_0 ++
  entries11_1 ++
  entries11_2 ++
  entries11_3 ++
  entries11_4 ++
  entries11_5 ++
  entries11_6 ++
  entries11_7

theorem entries11_checked : ∀ entry ∈ entries11, entry.Check := by
  unfold entries11
  simp only [List.forall_mem_append]
  exact ⟨entries11_0_checked, entries11_1_checked, entries11_2_checked, entries11_3_checked, entries11_4_checked, entries11_5_checked, entries11_6_checked, entries11_7_checked⟩

noncomputable def owner11 : Owner :=
  DirectRecipeTable.checkedOwner bank inside11 outside11 entries11 entries11_checked

theorem owner11_checked : owner11.Check :=
  DirectRecipeTable.checkedOwner_check bank inside11 outside11
    entries11 entries11_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
