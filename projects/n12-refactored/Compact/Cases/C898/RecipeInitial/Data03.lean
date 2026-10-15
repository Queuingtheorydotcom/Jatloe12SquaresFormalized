import Compact.Cases.C898.RecipeInitial.Batch03_00
import Compact.Cases.C898.RecipeInitial.Batch03_01
import Compact.Cases.C898.RecipeInitial.Batch03_02
import Compact.Cases.C898.RecipeInitial.Batch03_03
import Compact.Cases.C898.RecipeInitial.Batch03_04
import Compact.Cases.C898.RecipeInitial.Batch03_05
import Compact.Cases.C898.RecipeInitial.Batch03_06
import Compact.Cases.C898.RecipeInitial.Batch03_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries3 : List (DirectRecipeTable.Entry bank inside3 outside3) :=
  entries3_0 ++
  entries3_1 ++
  entries3_2 ++
  entries3_3 ++
  entries3_4 ++
  entries3_5 ++
  entries3_6 ++
  entries3_7

theorem entries3_checked : ∀ entry ∈ entries3, entry.Check := by
  unfold entries3
  simp only [List.forall_mem_append]
  exact ⟨entries3_0_checked, entries3_1_checked, entries3_2_checked, entries3_3_checked, entries3_4_checked, entries3_5_checked, entries3_6_checked, entries3_7_checked⟩

noncomputable def owner3 : Owner :=
  DirectRecipeTable.checkedOwner bank inside3 outside3 entries3 entries3_checked

theorem owner3_checked : owner3.Check :=
  DirectRecipeTable.checkedOwner_check bank inside3 outside3
    entries3 entries3_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
