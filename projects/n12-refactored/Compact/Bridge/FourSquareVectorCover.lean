import Compact.Bridge.FourSquareCase
import Compact.Bridge.MidpointCase
import S12.DomainEnumeration

/-! A small choice of two symbolic geometric arguments closes whole ownership
domains. Coverage is checked over the original certified ownership domains;
no archived list of refined domains is assumed as an entrance. -/
namespace N12Compact.FourSquareVectorCover
open S12
set_option Elab.async false

abbrev Recipe := Sum FourSquareCase.Data MidpointCase.Data

def Recipe.masks : Recipe → Fin 4 → Nat
  | .inl d => d.masks
  | .inr d => d.masks

def Recipe.owned : Recipe → Fin 4 → Finset Nat
  | .inl d => d.owned
  | .inr d => d.owned

def Recipe.Check (r : Recipe) (family : Finset Nat)
    (masks : List Nat) (vector : List (Finset Nat)) : Prop :=
  (match r with | .inl d => d.Check family | .inr d => d.Check family) ∧
  ∀ i, (r.masks i,r.owned i) ∈ masks.zip vector

instance (r : Recipe) (family : Finset Nat)
    (masks : List Nat) (vector : List (Finset Nat)) :
    Decidable (r.Check family masks vector) := by
  cases r <;> unfold Recipe.Check <;> infer_instance

private theorem zip_actual (masks : List Nat) (f : Nat → Finset Nat)
    (m : Nat) (v : Finset Nat) (member : (m,v) ∈ masks.zip (masks.map f)) : f m = v := by
  induction masks with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.map_cons,List.zip_cons_cons,List.mem_cons] at member
    rcases member with same | later
    · have hm := congrArg Prod.fst same
      have hv := congrArg Prod.snd same
      simp only [Prod.fst,Prod.snd] at hm hv
      rw [hm]
      exact hv.symm
    · exact ih later

def Check {family : Finset Nat} (ds : List (CertifiedDomain family))
    (recipes : List Recipe) : Prop :=
  ∀ v ∈ enumerateAssignments (ds.map CertifiedDomain.allowed) ∅,
    ∃ r ∈ recipes, r.Check family (ds.map CertifiedDomain.mask) v

instance {family : Finset Nat} (ds : List (CertifiedDomain family))
    (recipes : List Recipe) : Decidable (Check ds recipes) :=
  inferInstanceAs (Decidable (∀ v ∈ _, ∃ r ∈ recipes, _))

/-- Check each geometric pattern once. The ownership enumeration then checks
only four finite bindings, instead of repeatedly reducing geometric queries. -/
theorem check_of_parts {family : Finset Nat} (ds : List (CertifiedDomain family))
    (recipes : List Recipe)
    (geometry : ∀ r ∈ recipes,
      match r with | .inl d => d.Check family | .inr d => d.Check family)
    (coverage : ∀ v ∈ enumerateAssignments (ds.map CertifiedDomain.allowed) ∅,
      ∃ r ∈ recipes, ∀ i, (r.masks i,r.owned i) ∈
        (ds.map CertifiedDomain.mask).zip v) : Check ds recipes := by
  intro v hv
  obtain ⟨r,hr,hb⟩ := coverage v hv
  exact ⟨r,hr,geometry r hr,hb⟩

/-- Every remaining finite alternative ends in an actual packing contradiction.
Only four owner sets are selected from a whole vector; all other owners remain
present in the global domain cover and its pairwise-disjointness proof. -/
theorem impossible {family : Finset Nat} (ds : List (CertifiedDomain family))
    (members : ∀ d ∈ ds, d.mask ∈ family)
    (distinct : ds.Pairwise (fun a b => a.mask ≠ b.mask))
    (recipes : List Recipe) (checked : Check ds recipes)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family) : False := by
  let f : Nat → Finset Nat := fun m => natCombinedOwners p (ownerIndex p m)
  have actual := certified_domain_assignments_mem ds members distinct p hf
  obtain ⟨r,_,hr,hbinding⟩ := checked _ actual
  have owned (i : Fin 4) : f (r.masks i) = r.owned i := by
    apply zip_actual (ds.map CertifiedDomain.mask) f
    simpa only [List.map_map,Function.comp_def,f] using hbinding i
  cases r with
  | inl d => exact FourSquareCase.impossible_actual d family hr p hf owned
  | inr d => exact MidpointCase.impossible_actual d family hr p hf owned

#print axioms impossible
end N12Compact.FourSquareVectorCover
