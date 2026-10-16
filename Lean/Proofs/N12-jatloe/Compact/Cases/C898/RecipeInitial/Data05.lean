import Compact.Cases.C898.RecipeInitial.Batch05_00
import Compact.Cases.C898.RecipeInitial.Batch05_01
import Compact.Cases.C898.RecipeInitial.Batch05_02
import Compact.Cases.C898.RecipeInitial.Batch05_03
import Compact.Cases.C898.RecipeInitial.Batch05_04
import Compact.Cases.C898.RecipeInitial.Batch05_05
import Compact.Cases.C898.RecipeInitial.Batch05_06
import Compact.Cases.C898.RecipeInitial.Batch05_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries5 : List (DirectRecipeTable.Entry bank inside5 outside5) :=
  entries5_0 ++
  entries5_1 ++
  entries5_2 ++
  entries5_3 ++
  entries5_4 ++
  entries5_5 ++
  entries5_6 ++
  entries5_7

theorem entries5_checked : ∀ entry ∈ entries5, entry.Check := by
  unfold entries5
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries5_0_checked, entries5_1_checked, entries5_2_checked, entries5_3_checked, entries5_4_checked, entries5_5_checked, entries5_6_checked, entries5_7_checked⟩

noncomputable def owner5 : Owner :=
  DirectRecipeTable.checkedOwner bank inside5 outside5 entries5 entries5_checked

theorem owner5_checked : owner5.Check :=
  DirectRecipeTable.checkedOwner_check bank inside5 outside5
    entries5 entries5_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
