import Compact.Cases.C898.RecipeInitial.Batch08_00
import Compact.Cases.C898.RecipeInitial.Batch08_01
import Compact.Cases.C898.RecipeInitial.Batch08_02
import Compact.Cases.C898.RecipeInitial.Batch08_03
import Compact.Cases.C898.RecipeInitial.Batch08_04
import Compact.Cases.C898.RecipeInitial.Batch08_05
import Compact.Cases.C898.RecipeInitial.Batch08_06
import Compact.Cases.C898.RecipeInitial.Batch08_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries8 : List (DirectRecipeTable.Entry bank inside8 outside8) :=
  entries8_0 ++
  entries8_1 ++
  entries8_2 ++
  entries8_3 ++
  entries8_4 ++
  entries8_5 ++
  entries8_6 ++
  entries8_7

theorem entries8_checked : ∀ entry ∈ entries8, entry.Check := by
  unfold entries8
  simp only [List.forall_mem_append]
  exact ⟨entries8_0_checked, entries8_1_checked, entries8_2_checked, entries8_3_checked, entries8_4_checked, entries8_5_checked, entries8_6_checked, entries8_7_checked⟩

noncomputable def owner8 : Owner :=
  DirectRecipeTable.checkedOwner bank inside8 outside8 entries8 entries8_checked

theorem owner8_checked : owner8.Check :=
  DirectRecipeTable.checkedOwner_check bank inside8 outside8
    entries8 entries8_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
