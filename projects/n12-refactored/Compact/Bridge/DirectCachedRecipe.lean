import Compact.Bridge.DirectOwnerRecipe
import Compact.Core.PlanarBoundaryAuto
import Compact.Core.RowMaterializeSyntax
import Compact.Core.BoundaryHintSyntax

/-! Exact cached geometric recipes for full owner covers.

The base and forbidden forms are materialized once. Bounded, untrusted hint
selection removes impossible boundary lines only after the existing filter
checker validates every omission. Its complete retained-row list is cached
with an ordinary-kernel equality. Numeric batches inspect local constructors.
-/

namespace N12Compact.DirectPoseCover
open S12 IntegerSupport PlanarVertex PlanarVertexCheck PlanarVertexSparse

structure CachedRecipe (inside outside : List (ℚ × ℚ)) where
  recipe : Recipe inside
  base : List Form
  forbidden : List (List Form)
  base_exact : base = (recipe.root outside).base
  forbidden_exact : forbidden = (recipe.root outside).forbidden
  boundary : PlanarBoundaryHints.Cache
    (base.map Form.row) (forbidden.map (List.map Form.row))

/-- Keep the numeric checker independent of hint-discovery implementation. -/
def CachedRecipe.active {inside outside : List (ℚ × ℚ)}
    (cached : CachedRecipe inside outside) : List Row := cached.boundary.rows

def CachedRecipe.Check {inside outside : List (ℚ × ℚ)}
    (cached : CachedRecipe inside outside) : Prop :=
  BoxNormals (cached.base.map Form.row) ∧
  triangle (PairCheck (cached.base.map Form.row)
    (cached.forbidden.map (List.map Form.row))
    (cached.recipe.root outside).targetRows) cached.active ∧
  (cached.recipe.root outside).strictOK

instance {inside outside : List (ℚ × ℚ)} (cached : CachedRecipe inside outside) :
    Decidable cached.Check := by
  unfold CachedRecipe.Check BoxNormals
  infer_instance

theorem CachedRecipe.checked {inside outside : List (ℚ × ℚ)}
    (cached : CachedRecipe inside outside) (checked : cached.Check) :
    (cached.recipe.root outside).Check inside outside := by
  obtain ⟨box, numeric, strict⟩ := checked
  have full := cached.boundary.toCheck numeric
  apply cached.recipe.checked outside
  refine ⟨?_, ?_, strict⟩
  · simpa only [cached.base_exact, Root.baseRows] using box
  · simpa only [cached.base_exact, cached.forbidden_exact,
      Root.baseRows, Root.forbiddenRows] using full

def checkedCachedRoots (inside outside : List (ℚ × ℚ)) :
    (recipes : List (CachedRecipe inside outside)) →
    (∀ recipe ∈ recipes, recipe.Check) →
    List {root : Root // root.Check inside outside}
  | [], _ => []
  | recipe :: rest, checked =>
      ⟨recipe.recipe.root outside, recipe.checked (checked recipe (by simp))⟩ ::
      checkedCachedRoots inside outside rest
        (fun other member => checked other (List.mem_cons_of_mem recipe member))

def checkedCachedOwner (inside outside : List (ℚ × ℚ))
    (recipes : List (CachedRecipe inside outside))
    (checked : ∀ recipe ∈ recipes, recipe.Check) : Owner :=
  ⟨inside, outside, checkedCachedRoots inside outside recipes checked⟩

/-- Source notation for a cached recipe. Materialization emits data only;
all cache equalities are checked by ordinary `decide +kernel` proofs. -/
syntax "cache_recipe%(" term "," term ")" : term

macro_rules
  | `(cache_recipe%($recipe:term, $outside:term)) =>
    `({ recipe := $recipe
        base := materialize_forms% (($recipe).root $outside).base
        forbidden := materialize_forms% (($recipe).root $outside).forbidden
        base_exact := by decide +kernel
        forbidden_exact := by decide +kernel
        boundary := boundary_cache%(
          ((materialize_forms% (($recipe).root $outside).base).map Form.row)
          ,
          ((materialize_forms% (($recipe).root $outside).forbidden).map
            (List.map Form.row))) })

#print axioms CachedRecipe.checked
end N12Compact.DirectPoseCover
