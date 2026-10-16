import Compact.Completion.OtherCases.C705716.RefinedDomains

namespace N12Compact.Completion.OtherCases.C705716
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem domain_masks (b : Bool) : (domains b).map CertifiedDomain.mask =
    [1,2,12,16,32,192,(if b then 512 else 256),(if b then 3328 else 3584),
      4096,8192,16384,32768] := by
  rfl

theorem domain_members (b : Bool) : ∀ d ∈ domains b, d.mask ∈ family b := by
  intro d hd
  obtain ⟨n,_,rfl⟩ := List.mem_map.mp hd
  exact n.member

theorem domain_distinct (b : Bool) : (domains b).Pairwise (fun a c => a.mask ≠ c.mask) := by
  have h : ((domains b).map CertifiedDomain.mask).Pairwise (fun a c => a ≠ c) := by
    rw [domain_masks]
    cases b <;> decide +kernel
  simpa only [List.pairwise_map] using h

def expectedVector (b : Bool) : List (Finset Nat) :=
  [{2,12},{0,10},∅,{7,17},{9,19},∅,{4,(if b then 16 else 13)},
    {5,(if b then 13 else 16)},{1,11},{6,15},{8,18},{3,14}]

private theorem complete_singletons (b : Bool) :
    (domains b).map CertifiedDomain.allowed = (expectedVector b).map (fun s => [s]) := by
  cases b <;> decide +kernel

private theorem compact_cover (b : Bool) :
    ∀ v ∈ enumerateAssignments ((domains b).map CertifiedDomain.allowed) ∅, v = expectedVector b := by
  rw [complete_singletons]
  cases b <;> decide +kernel

def actualVector (b : Bool) (p : NormalizedPacking) : List (Finset Nat) :=
  [1,2,12,16,32,192,(if b then 512 else 256),(if b then 3328 else 3584),
    4096,8192,16384,32768].map (fun m => natCombinedOwners p (ownerIndex p m))

theorem actual_vector_map (b : Bool) (p : NormalizedPacking) :
    (domains b).map (fun d => natCombinedOwners p (ownerIndex p d.mask)) = actualVector b p := by
  have h := congrArg (List.map (fun m => natCombinedOwners p (ownerIndex p m))) (domain_masks b)
  simpa only [actualVector,List.map_map,Function.comp_def] using h

theorem actual_entry (b : Bool) (p : NormalizedPacking) (j : Fin 12) :
    (actualVector b p)[j.val]! = natCombinedOwners p (ownerIndex p (ownerCode b j)) := by
  fin_cases j <;> rfl

/-- The unique auxiliary labels are conclusions about the true packing. -/
theorem actual_cover (b : Bool) (p : NormalizedPacking) (hf : codedMarkerFamily p = family b) :
    actualVector b p = expectedVector b := by
  have member := certified_domain_assignments_mem (domains b) (domain_members b) (domain_distinct b) p hf
  have cover := compact_cover b _ member
  rw [actual_vector_map] at cover
  exact cover

end
end N12Compact.Completion.OtherCases.C705716
