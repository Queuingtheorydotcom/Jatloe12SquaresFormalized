import Compact.Cases.C898.RecipeInitial.Batch07_00
import Compact.Cases.C898.RecipeInitial.Batch07_01
import Compact.Cases.C898.RecipeInitial.Batch07_02
import Compact.Cases.C898.RecipeInitial.Batch07_03
import Compact.Cases.C898.RecipeInitial.Batch07_04
import Compact.Cases.C898.RecipeInitial.Batch07_05
import Compact.Cases.C898.RecipeInitial.Batch07_06
import Compact.Cases.C898.RecipeInitial.Batch07_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries7 : List (DirectRecipeTable.Entry bank inside7 outside7) :=
  entries7_0 ++
  entries7_1 ++
  entries7_2 ++
  entries7_3 ++
  entries7_4 ++
  entries7_5 ++
  entries7_6 ++
  entries7_7

theorem entries7_checked : ∀ entry ∈ entries7, entry.Check := by
  unfold entries7
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries7_0_checked, entries7_1_checked, entries7_2_checked, entries7_3_checked, entries7_4_checked, entries7_5_checked, entries7_6_checked, entries7_7_checked⟩

noncomputable def owner7 : Owner :=
  DirectRecipeTable.checkedOwner bank inside7 outside7 entries7 entries7_checked

theorem owner7_checked : owner7.Check :=
  DirectRecipeTable.checkedOwner_check bank inside7 outside7
    entries7 entries7_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
