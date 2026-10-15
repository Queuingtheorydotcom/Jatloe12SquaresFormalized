import Compact.Cases.C898.RecipeInitial.Batch00_00
import Compact.Cases.C898.RecipeInitial.Batch00_01
import Compact.Cases.C898.RecipeInitial.Batch00_02
import Compact.Cases.C898.RecipeInitial.Batch00_03
import Compact.Cases.C898.RecipeInitial.Batch00_04
import Compact.Cases.C898.RecipeInitial.Batch00_05
import Compact.Cases.C898.RecipeInitial.Batch00_06
import Compact.Cases.C898.RecipeInitial.Batch00_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries0 : List (DirectRecipeTable.Entry bank inside0 outside0) :=
  entries0_0 ++
  entries0_1 ++
  entries0_2 ++
  entries0_3 ++
  entries0_4 ++
  entries0_5 ++
  entries0_6 ++
  entries0_7

theorem entries0_checked : ∀ entry ∈ entries0, entry.Check := by
  unfold entries0
  simp only [List.forall_mem_append]
  exact ⟨entries0_0_checked, entries0_1_checked, entries0_2_checked, entries0_3_checked, entries0_4_checked, entries0_5_checked, entries0_6_checked, entries0_7_checked⟩

noncomputable def owner0 : Owner :=
  DirectRecipeTable.checkedOwner bank inside0 outside0 entries0 entries0_checked

theorem owner0_checked : owner0.Check :=
  DirectRecipeTable.checkedOwner_check bank inside0 outside0
    entries0 entries0_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
