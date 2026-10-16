import Compact.Cases.C898.RecipeInitial.Batch01_00
import Compact.Cases.C898.RecipeInitial.Batch01_01
import Compact.Cases.C898.RecipeInitial.Batch01_02
import Compact.Cases.C898.RecipeInitial.Batch01_03
import Compact.Cases.C898.RecipeInitial.Batch01_04
import Compact.Cases.C898.RecipeInitial.Batch01_05
import Compact.Cases.C898.RecipeInitial.Batch01_06
import Compact.Cases.C898.RecipeInitial.Batch01_07

/-! One semantic record per original angle: angle ID, original input indices,
and optional original reduced pose ID. Generic checked caches and owner
assembly retain the full original geometric and ownership obligations. -/
namespace N12Compact.C898RecipeInitial
open S12 S12Pilot DirectPoseCover C898DirectInitial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

noncomputable def entries1 : List (DirectRecipeTable.Entry bank inside1 outside1) :=
  entries1_0 ++
  entries1_1 ++
  entries1_2 ++
  entries1_3 ++
  entries1_4 ++
  entries1_5 ++
  entries1_6 ++
  entries1_7

theorem entries1_checked : ∀ entry ∈ entries1, entry.Check := by
  unfold entries1
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨entries1_0_checked, entries1_1_checked, entries1_2_checked, entries1_3_checked, entries1_4_checked, entries1_5_checked, entries1_6_checked, entries1_7_checked⟩

noncomputable def owner1 : Owner :=
  DirectRecipeTable.checkedOwner bank inside1 outside1 entries1 entries1_checked

theorem owner1_checked : owner1.Check :=
  DirectRecipeTable.checkedOwner_check bank inside1 outside1
    entries1 entries1_checked C898Initial.angles64_cover_kernel

end N12Compact.C898RecipeInitial
