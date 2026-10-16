import Compact.Cases.C898.RecipeInitial.Batch06_00
import Compact.Cases.C898.RecipeInitial.Batch06_01
import Compact.Cases.C898.RecipeInitial.Batch06_02
import Compact.Cases.C898.RecipeInitial.Batch06_03
import Compact.Cases.C898.RecipeInitial.Batch06_04
import Compact.Cases.C898.RecipeInitial.Batch06_05
import Compact.Cases.C898.RecipeInitial.Batch06_06
import Compact.Cases.C898.RecipeInitial.Batch06_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries6 : List (DirectRecipeTable.Entry bank inside6 outside6) :=
  entries6_0 ++
  entries6_1 ++
  entries6_2 ++
  entries6_3 ++
  entries6_4 ++
  entries6_5 ++
  entries6_6 ++
  entries6_7

theorem entries6_checked : ∀ entry ∈ entries6, entry.Check := by
  unfold entries6
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries6_0_checked, entries6_1_checked, entries6_2_checked, entries6_3_checked, entries6_4_checked, entries6_5_checked, entries6_6_checked, entries6_7_checked⟩

noncomputable def owner6 : Owner :=
  DirectRecipeTable.checkedOwner bank inside6 outside6 entries6 entries6_checked

theorem owner6_checked : owner6.Check :=
  DirectRecipeTable.checkedOwner_check bank inside6 outside6
    entries6 entries6_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
