import Compact.Bridge.DirectCachedRecipe

/-! Shared-pose recipes for direct initial covers.

One semantic record chooses an angle, original input indices and an optional
existing pose. Target rows and their order come from the shared dictionary;
there is no owner-local target pool or second list of target-row identifiers.
Every cached value retains an ordinary-kernel equality to the original root.
Clients check numeric tables in small batches and separately prove complete
angle coverage and equality to the original reduced domain.
-/

namespace N12Compact.DirectRecipeTable

open S12 S12Pilot IntegerSupport PlanarVertex PlanarVertexCheck PlanarVertexSparse
open DirectPoseCover

/-- Exact view of an existing pose dictionary. The equality is a real proof
obligation, not a declaration that proposed target rows match old source. -/
structure Bank (angleCount poseCount : Nat) where
  angles : Fin angleCount → {w : AngleEnclosure // w.Check}
  poseAngle : Fin poseCount → Fin angleCount
  forms : Fin poseCount → List Form
  poses : Fin poseCount → PoseLeaf
  pose_exact : ∀ i, poses i = ⟨angles (poseAngle i), (forms i).map Form.decode⟩

/-- Raw choices only. Input bounds and target-angle compatibility are checked
once by the generic constructor, rather than proved at every literal index. -/
structure Spec (angleCount poseCount : Nat) where
  angle : Fin angleCount
  inputIndices : List Nat
  target : Option (Fin poseCount)
  deriving DecidableEq

variable {angleCount poseCount : Nat}

def Spec.Check (spec : Spec angleCount poseCount)
    (bank : Bank angleCount poseCount) (inside : List (ℚ × ℚ)) : Prop :=
  (∀ i ∈ spec.inputIndices, i < (poseInputs (bank.angles spec.angle).val inside).length) ∧
  ∀ i ∈ spec.target.toList, spec.angle = bank.poseAngle i

instance (spec : Spec angleCount poseCount) (bank : Bank angleCount poseCount)
    (inside : List (ℚ × ℚ)) : Decidable (spec.Check bank inside) := by
  unfold Spec.Check
  letI : Decidable (∀ i ∈ spec.inputIndices,
      i < (poseInputs (bank.angles spec.angle).val inside).length) :=
    List.decidableBAll _ spec.inputIndices
  letI : Decidable (∀ i ∈ spec.target.toList, spec.angle = bank.poseAngle i) :=
    List.decidableBAll _ spec.target.toList
  infer_instance

def Bank.recipe (bank : Bank angleCount poseCount) (inside : List (ℚ × ℚ))
    (spec : Spec angleCount poseCount) (checked : spec.Check bank inside) :
    Recipe inside :=
  ⟨bank.angles spec.angle,
   spec.inputIndices.attach.map (fun i => ⟨i.val, checked.1 i.val i.property⟩),
   spec.target.map bank.forms⟩

/-- In particular an empty angle root contributes no target, and a retained
root contributes exactly its original pose, including its angle and row order. -/
theorem Bank.recipe_leaves (bank : Bank angleCount poseCount)
    (inside outside : List (ℚ × ℚ)) (spec : Spec angleCount poseCount)
    (checked : spec.Check bank inside) :
    ((bank.recipe inside spec checked).root outside).leaves =
      spec.target.toList.map bank.poses := by
  cases ht : spec.target with
  | none =>
      simp [Bank.recipe, Recipe.root, sourceRoot, Root.leaves, ht]
  | some i =>
      have ha : spec.angle = bank.poseAngle i := checked.2 i (by simp [ht])
      simp [Bank.recipe, Recipe.root, sourceRoot, Root.leaves, ht, ha, bank.pose_exact i]

/-- The original cache plus a materialized target. The fourth equality avoids
repeated dictionary unfolding during the numeric vertex tests. -/
structure Entry (bank : Bank angleCount poseCount) (inside outside : List (ℚ × ℚ)) where
  spec : Spec angleCount poseCount
  spec_checked : spec.Check bank inside
  cached : CachedRecipe inside outside
  recipe_exact : cached.recipe = bank.recipe inside spec spec_checked
  targets : List Row
  targets_exact : targets = (cached.recipe.root outside).targetRows

def Entry.Check {bank : Bank angleCount poseCount} {inside outside : List (ℚ × ℚ)}
    (entry : Entry bank inside outside) : Prop :=
  BoxNormals (entry.cached.base.map Form.row) ∧
  triangle (PairCheck (entry.cached.base.map Form.row)
    (entry.cached.forbidden.map (List.map Form.row)) entry.targets) entry.cached.active ∧
  (entry.cached.recipe.root outside).strictOK

instance {bank : Bank angleCount poseCount} {inside outside : List (ℚ × ℚ)}
    (entry : Entry bank inside outside) : Decidable entry.Check := by
  unfold Entry.Check BoxNormals
  infer_instance

theorem Entry.cached_checked {bank : Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)} (entry : Entry bank inside outside)
    (checked : entry.Check) : entry.cached.Check := by
  obtain ⟨box, numeric, strict⟩ := checked
  refine ⟨box, ?_, strict⟩
  simpa only [entry.targets_exact] using numeric

theorem Entry.leaves_exact {bank : Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)} (entry : Entry bank inside outside) :
    (entry.cached.recipe.root outside).leaves = entry.spec.target.toList.map bank.poses := by
  rw [entry.recipe_exact]
  exact bank.recipe_leaves inside outside entry.spec entry.spec_checked

theorem Entry.angle_exact {bank : Bank angleCount poseCount}
    {inside outside : List (ℚ × ℚ)} (entry : Entry bank inside outside) :
    (entry.cached.recipe.root outside).angle = bank.angles entry.spec.angle := by
  rw [entry.recipe_exact]
  rfl

def checkedRoots (bank : Bank angleCount poseCount) (inside outside : List (ℚ × ℚ)) :
    (entries : List (Entry bank inside outside)) →
    (∀ entry ∈ entries, entry.Check) → List {root : Root // root.Check inside outside}
  | [], _ => []
  | entry :: rest, checked =>
      ⟨entry.cached.recipe.root outside,
        entry.cached.checked (entry.cached_checked (checked entry (by simp)))⟩ ::
      checkedRoots bank inside outside rest
        (fun other member => checked other (List.mem_cons_of_mem entry member))

def checkedOwner (bank : Bank angleCount poseCount) (inside outside : List (ℚ × ℚ))
    (entries : List (Entry bank inside outside))
    (checked : ∀ entry ∈ entries, entry.Check) : Owner :=
  ⟨inside, outside, checkedRoots bank inside outside entries checked⟩

/-- Exact domain binding reduces to a small list of original pose identifiers;
neither the numeric proof terms nor the target row lists enter that identity. -/
theorem checkedRoots_leaves (bank : Bank angleCount poseCount)
    (inside outside : List (ℚ × ℚ)) (entries : List (Entry bank inside outside)) :
    ∀ checked : ∀ entry ∈ entries, entry.Check,
      (checkedRoots bank inside outside entries checked).flatMap (fun root => root.val.leaves) =
        entries.flatMap (fun entry => entry.spec.target.toList.map bank.poses) := by
  induction entries with
  | nil => intro checked; rfl
  | cons entry rest ih =>
      intro checked
      simp only [checkedRoots, List.flatMap_cons]
      rw [entry.leaves_exact, ih]

theorem checkedOwner_leaves (bank : Bank angleCount poseCount)
    (inside outside : List (ℚ × ℚ)) (entries : List (Entry bank inside outside))
    (checked : ∀ entry ∈ entries, entry.Check) :
    (checkedOwner bank inside outside entries checked).leaves =
      entries.flatMap (fun entry => entry.spec.target.toList.map bank.poses) :=
  checkedRoots_leaves bank inside outside entries checked

theorem checkedRoots_angles (bank : Bank angleCount poseCount)
    (inside outside : List (ℚ × ℚ)) (entries : List (Entry bank inside outside)) :
    ∀ checked : ∀ entry ∈ entries, entry.Check,
      (checkedRoots bank inside outside entries checked).map (fun root => root.val.angle.val) =
        entries.map (fun entry => (bank.angles entry.spec.angle).val) := by
  induction entries with
  | nil => intro checked; rfl
  | cons entry rest ih =>
      intro checked
      simp only [checkedRoots, List.map_cons]
      rw [entry.angle_exact, ih]

/-- Full closed-grid coverage is checked on the small angle-ID table. -/
theorem checkedOwner_check (bank : Bank angleCount poseCount)
    (inside outside : List (ℚ × ℚ)) (entries : List (Entry bank inside outside))
    (checked : ∀ entry ∈ entries, entry.Check)
    (cover : CoversInterval 0 1
      (entries.map (fun entry => (bank.angles entry.spec.angle).val))) :
    (checkedOwner bank inside outside entries checked).Check := by
  change CoversInterval 0 1
    ((checkedRoots bank inside outside entries checked).map (fun root => root.val.angle.val))
  rw [checkedRoots_angles]
  exact cover

/-- A table literal contains one semantic Spec per angle. Expansion delegates
to the existing checked materializer; no numerical or geometric claim is
accepted by the notation. Keep the table at the measured eight-root batch size.
-/
syntax "cached_recipe_table%(" term "," term "," term ")[" term,* "]" : term

/-- Finish the small input-bound and angle checks before a materializer inspects
the recipe. A nested `by decide` otherwise remains a postponed metavariable
when `materialize_forms%` checks that its argument is closed. This elaborator
does not evaluate a proof or weaken any of the later cache equalities. -/
syntax (name := closedRecipe) "closed_recipe% " term : term

open Lean Elab Term Meta in
elab_rules : term
  | `(closed_recipe% $input:term) => do
      let value ← instantiateMVars (← elabTermAndSynthesize input none)
      if value.hasMVar || value.hasFVar then
        throwErrorAt input "closed_recipe% requires a closed concrete recipe"
      return value

macro_rules
  | `(cached_recipe_table%($bank:term, $inside:term, $outside:term)[$specs:term,*]) => do
      let entries ← specs.getElems.mapM fun spec => do
        let recipe ← `(closed_recipe% (Bank.recipe $bank $inside $spec (by decide +kernel)))
        `(({ spec := $spec
             spec_checked := by decide +kernel
             cached := cache_recipe%($recipe, $outside)
             recipe_exact := rfl
             targets := materialize_rows% (($recipe).root $outside).targetRows
             targets_exact := by decide +kernel } : Entry $bank $inside $outside))
      `([$entries,*])

#print axioms Bank.recipe_leaves
#print axioms Entry.cached_checked
#print axioms checkedOwner_leaves

end N12Compact.DirectRecipeTable
