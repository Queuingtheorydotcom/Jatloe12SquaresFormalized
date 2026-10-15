import Compact.Cases.MergedLower.Helpers
import Compact.Bridge.FourSquareCaseHighRight
import Compact.Bridge.EndpointHighRightCase
import S12.DomainEnumeration

/-! Original case684 has six remaining ownership vectors. After a half-turn,
four use the existing upper-row template, and two use a strict unit-height
span. The right singleton supplies both right points by strict convexity.
Every domain below is derived from original checked ownership specifications. -/
namespace N12Compact.Endpoint684
open S12 RelaxedOwnerDomain MergedLower
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def family : Finset Nat := {1,2,12,16,32,192,256,512,3072,4096,16384,32768}

def domain1 : CertifiedDomain family :=
  direct family combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain2 : CertifiedDomain family :=
  direct family combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain16 : CertifiedDomain family :=
  halfturned family 16 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain32 : CertifiedDomain family :=
  halfturned family 32 combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain4096 : CertifiedDomain family :=
  direct family combinedSpec17 combinedSpec17_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain16384 : CertifiedDomain family :=
  direct family combinedSpec21 combinedSpec21_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain32768 : CertifiedDomain family :=
  direct family combinedSpec24 combinedSpec24_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain256 : CertifiedDomain family :=
  direct family combinedSpec6 combinedSpec6_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domain512 : CertifiedDomain family :=
  direct family combinedSpec8 combinedSpec8_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domains : List (CertifiedDomain family) :=
  [domain1,domain2,domain16,domain32,domain4096,domain16384,domain32768,domain256,domain512]

theorem domains_members : ∀ d ∈ domains, d.mask ∈ family := by decide +kernel
theorem domains_distinct : domains.Pairwise (fun a b => a.mask ≠ b.mask) := by
  decide +kernel

def roles : Fin 4 → Nat := ![256,512,16384,2]

def upper (owned : Fin 4 → Finset Nat) : FourSquareCaseHighRight.Data :=
  ⟨⟨false,true,true⟩,roles,owned,32⟩

def endpoint (owned : Fin 4 → Finset Nat) : EndpointHighRightCase.Data :=
  ⟨⟨false,true,true⟩,roles,owned⟩

def patterns : List (Fin 4 → Finset Nat) :=
  [![{4,13},{6,15},{8,18},{0,10}],
   ![{4,13},{6,16},{8,18},{0,10}],
   ![{4,13},{6,15,16},{8,18},{0,10}],
   ![{4,13,15},{6,16},{8,18},{0,10}],
   ![{4,13,16},{6,15},{8,18},{0,10}],
   ![{4,13},{6,15},{8,16,18},{0,10}]]

theorem patterns_checked : ∀ owned ∈ patterns,
    (upper owned).Check family ∨ (endpoint owned).Check family := by
  decide +kernel

theorem patterns_cover :
    ∀ v ∈ enumerateAssignments (domains.map CertifiedDomain.allowed) ∅,
      ∃ owned ∈ patterns, ∀ i, (roles i,owned i) ∈
        (domains.map CertifiedDomain.mask).zip v := by
  decide +kernel

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

theorem case684_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : False := by
  let f : Nat → Finset Nat := fun m => natCombinedOwners p (ownerIndex p m)
  have actual := certified_domain_assignments_mem domains domains_members domains_distinct p hf
  obtain ⟨owned,member,binding⟩ := patterns_cover _ actual
  have equal (i : Fin 4) : f (roles i) = owned i := by
    apply zip_actual (domains.map CertifiedDomain.mask) f
    simpa only [List.map_map,Function.comp_def,f] using binding i
  rcases patterns_checked owned member with upperCase | endpointCase
  · exact FourSquareCaseHighRight.impossible_of_owned (upper owned) family upperCase p hf equal
  · exact EndpointHighRightCase.impossible_actual (endpoint owned) family endpointCase p hf equal

#print axioms case684_impossible
end
end N12Compact.Endpoint684
