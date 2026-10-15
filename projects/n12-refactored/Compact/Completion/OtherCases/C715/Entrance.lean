import Compact.Completion.OtherCases.C715.RefinedDomains

/-! Final genuine C715 coverage: fourteen full assignments, with both local
branches and every possible additional F point retained. -/
namespace N12Compact.Completion.OtherCases.C715
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem domain_masks : domains.map CertifiedDomain.mask =
    [1,2,12,16,32,192,512,2304,4096,8192,17408,32768] := by
  rfl

theorem domain_members : ∀ d ∈ domains, d.mask ∈ family := by
  intro d hd
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp hd
  exact n.member

theorem domain_distinct : domains.Pairwise (fun a b => a.mask ≠ b.mask) := by
  have h : (domains.map CertifiedDomain.mask).Pairwise (fun a b => a ≠ b) := by
    rw [domain_masks]
    decide +kernel
  simpa only [List.pairwise_map] using h

def CoverProperty (v : List (Finset Nat)) : Prop :=
  5 ∈ v[10]! ∧ 6 ∈ v[9]! ∧ 9 ∈ v[4]! ∧
    ((16 ∈ v[6]! ∧ 18 ∈ v[10]!) ∨ (16 ∈ v[10]! ∧ 18 ∈ v[6]!))

instance (v : List (Finset Nat)) : Decidable (CoverProperty v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- This is a finite coverage proof of genuine, independently certified
owner domains. It does not assume that a recovered survivor table was exhaustive. -/
private theorem compact_cover :
    ∀ v ∈ enumerateAssignments (domains.map CertifiedDomain.allowed) ∅, CoverProperty v := by
  decide +kernel

def actualVector (p : NormalizedPacking) : List (Finset Nat) :=
  [1,2,12,16,32,192,512,2304,4096,8192,17408,32768].map
    (fun m => natCombinedOwners p (ownerIndex p m))

theorem actual_vector_map (p : NormalizedPacking) :
    domains.map (fun d => natCombinedOwners p (ownerIndex p d.mask)) = actualVector p := by
  have h := congrArg (List.map (fun m => natCombinedOwners p (ownerIndex p m))) domain_masks
  simpa only [actualVector,List.map_map] using h

theorem actual_entry (p : NormalizedPacking) (j : Fin 12) :
    (actualVector p)[j.val]! = natCombinedOwners p (ownerIndex p (ownerCode j)) := by
  fin_cases j <;> rfl

/-- The three forced F memberships and the G6/G8 alternatives all concern
the actual original marker owners. Additional F ownership remains permitted. -/
theorem actual_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    CoverProperty (actualVector p) := by
  have h := certified_domain_assignments_mem domains domain_members domain_distinct p hf
  have cover := compact_cover _ h
  rw [actual_vector_map] at cover
  exact cover

end
end N12Compact.Completion.OtherCases.C715
