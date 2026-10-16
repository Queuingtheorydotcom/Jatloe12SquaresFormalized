import Compact.Bridge.DirectPoseForms
import Compact.Core.RowSyntax

/-! Shared assembly of direct initial covers.

A recipe contains only the varying geometric choices. One bounded-list check
per owner certifies all recipes, and the common constructor below supplies the
original Root.Check proofs. Numerical target rows can be read from a small
local pool shared by every angle of that owner.
-/

namespace N12Compact.DirectPoseCover

open S12 IntegerSupport PlanarVertex

structure Recipe (inside : List (ℚ × ℚ)) where
  angle : {w : AngleEnclosure // w.Check}
  indices : List (Fin (poseInputs angle.val inside).length)
  result : Option (List Form)

def Recipe.root {inside : List (ℚ × ℚ)} (outside : List (ℚ × ℚ))
    (recipe : Recipe inside) : Root :=
  sourceRoot recipe.angle inside outside recipe.indices recipe.result

def Recipe.Check {inside : List (ℚ × ℚ)} (outside : List (ℚ × ℚ))
    (recipe : Recipe inside) : Prop :=
  BoxNormals (recipe.root outside).baseRows ∧
  PlanarVertexCheck.Check (recipe.root outside).baseRows
    (recipe.root outside).forbiddenRows (recipe.root outside).targetRows ∧
  (recipe.root outside).strictOK

instance {inside : List (ℚ × ℚ)} (outside : List (ℚ × ℚ))
    (recipe : Recipe inside) : Decidable (recipe.Check outside) := by
  unfold Recipe.Check BoxNormals
  infer_instance

theorem Recipe.checked {inside : List (ℚ × ℚ)} (outside : List (ℚ × ℚ))
    (recipe : Recipe inside) (checked : recipe.Check outside) :
    (recipe.root outside).Check inside outside :=
  sourceRoot_check recipe.angle inside outside recipe.indices recipe.result
    checked.1 checked.2.1 checked.2.2

/-- Recursion shares the semantic assembly proof for every recipe. -/
def checkedRoots (inside outside : List (ℚ × ℚ)) :
    (recipes : List (Recipe inside)) →
    (∀ recipe ∈ recipes, recipe.Check outside) →
    List {root : Root // root.Check inside outside}
  | [], _ => []
  | recipe :: rest, checked =>
      ⟨recipe.root outside, recipe.checked outside (checked recipe (by simp))⟩ ::
      checkedRoots inside outside rest
        (fun other member => checked other (List.mem_cons_of_mem recipe member))

def checkedOwner (inside outside : List (ℚ × ℚ))
    (recipes : List (Recipe inside))
    (checked : ∀ recipe ∈ recipes, recipe.Check outside) : Owner :=
  ⟨inside, outside, checkedRoots inside outside recipes checked⟩

/-- Pool indices choose concrete target forms only. Out-of-bounds defaults
cannot certify the wrong historical output: every client must prove exact
equality of its resulting leaves to the original reduced pose domain. -/
def poolForms (pool : Array (Array (Row × Nat))) (indices : List Nat) : List Form :=
  indices.map (fun index =>
    let row := RowSyntax.lookup pool index
    ⟨row.1, row.2⟩)

#print axioms Recipe.checked
end N12Compact.DirectPoseCover
