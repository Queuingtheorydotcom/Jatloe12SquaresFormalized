import Compact.Bridge.PrefixCoverage
import Mathlib.Data.List.Forall2

/-! Reordering the same twelve owners puts the constrained wall domains
before the central domains. Neither ownership nor its allowances changes. -/
namespace N12Compact.PrefixCoverage
set_option Elab.async false

def reorder {α : Type} (v : List α) : List α :=
  v.take 2 ++ (v.drop 2).drop 6 ++ (v.drop 2).take 6

def unorder {α : Type} (v : List α) : List α :=
  v.take 2 ++ (v.drop 2).drop 4 ++ (v.drop 2).take 4

theorem reorder_perm {α : Type} (v : List α) : (reorder v).Perm v := by
  have tail : ((v.drop 2).drop 6 ++ (v.drop 2).take 6).Perm (v.drop 2) := by
    simpa only [List.take_append_drop] using
      (List.perm_append_comm : ((v.drop 2).drop 6 ++ (v.drop 2).take 6).Perm
        ((v.drop 2).take 6 ++ (v.drop 2).drop 6))
  simpa only [reorder,List.append_assoc,List.take_append_drop] using
    tail.append_left (v.take 2)

theorem reorder_allowed {α β : Type} {R : α → β → Prop} {a : List α} {ds : List β}
    (h : List.Forall₂ R a ds) : List.Forall₂ R (reorder a) (reorder ds) := by
  simpa only [reorder,List.append_assoc] using List.rel_append (List.forall₂_take 2 h)
    (List.rel_append (List.forall₂_drop 6 (List.forall₂_drop 2 h))
      (List.forall₂_take 6 (List.forall₂_drop 2 h)))

theorem reorder_pairwise (v : List (Finset Nat)) (h : v.Pairwise Disjoint) :
    (reorder v).Pairwise Disjoint :=
  h.perm (reorder_perm v).symm (fun h => h.symm)

theorem unorder_reorder {α : Type} (v : List α) (length : v.length = 12) :
    unorder (reorder v) = v := by
  let f : Fin 12 → α := fun i => v[i.val]'(by omega)
  have shape : List.ofFn f = v := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using length.symm
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  rw [← shape]
  rfl

#print axioms unorder_reorder
end N12Compact.PrefixCoverage
