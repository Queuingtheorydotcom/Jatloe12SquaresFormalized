import Compact.Cases.C898.RecipeInitial.Batch09_00
import Compact.Cases.C898.RecipeInitial.Batch09_01
import Compact.Cases.C898.RecipeInitial.Batch09_02
import Compact.Cases.C898.RecipeInitial.Batch09_03
import Compact.Cases.C898.RecipeInitial.Batch09_04
import Compact.Cases.C898.RecipeInitial.Batch09_05
import Compact.Cases.C898.RecipeInitial.Batch09_06
import Compact.Cases.C898.RecipeInitial.Batch09_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries9 : List (DirectRecipeTable.Entry bank inside9 outside9) :=
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
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries9_0_checked, entries9_1_checked, entries9_2_checked, entries9_3_checked, entries9_4_checked, entries9_5_checked, entries9_6_checked, entries9_7_checked⟩

noncomputable def owner9 : Owner :=
  DirectRecipeTable.checkedOwner bank inside9 outside9 entries9 entries9_checked

theorem owner9_checked : owner9.Check :=
  DirectRecipeTable.checkedOwner_check bank inside9 outside9
    entries9 entries9_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
