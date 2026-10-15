import Completion.Cases.C981.Ownership
import Completion.Cases.C981.DomainReuse
import Compact.Bridge.C981DomainReuse.Subset
import S12.DomainSpecData
import S12.DomainEnumeration

namespace S12Completion.C981
open S12 S12Pilot
open S12Completion.DomainReuse
noncomputable section

theorem auxiliary_budget_eq (k : Fin 2) :
    (N12Compact.C981DomainSubset.case976Family ∩ auxExempt k).card = (family ∩ auxExempt k).card := by
  fin_cases k <;> decide

def domain0 : CertifiedDomain family :=
  .ofCombined _ combinedSpec1 combinedSpec1_checked (by decide)

def domain1 : CertifiedDomain family :=
  .ofCombined _ combinedSpec3 combinedSpec3_checked (by decide)

def corner2 : CertifiedDomain family :=
  .ofDirectProduct _ N12Compact.C981DomainSubset.single976_2_0 N12Compact.C981DomainSubset.single976_2_1
    (direct_check_transport _ _ _ 0 (auxiliary_budget_eq 0) N12Compact.C981DomainSubset.single976_2_0_checked)
    (direct_check_transport _ _ _ 1 (auxiliary_budget_eq 1) N12Compact.C981DomainSubset.single976_2_1_checked) rfl

def domain2 : CertifiedDomain family := refineQueries corner2
  [⟨N12Compact.C981DomainSubset.query976_230,N12Compact.C981DomainSubset.query976_230_checked⟩,⟨N12Compact.C981DomainSubset.query976_231,N12Compact.C981DomainSubset.query976_231_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_232,N12Compact.C981DomainSubset.query976_232_checked⟩] (by decide)

def corner3 : CertifiedDomain family :=
  .ofDirectProduct _ N12Compact.C981DomainSubset.single976_3_0 N12Compact.C981DomainSubset.single976_3_1
    (direct_check_transport _ _ _ 0 (auxiliary_budget_eq 0) N12Compact.C981DomainSubset.single976_3_0_checked)
    (direct_check_transport _ _ _ 1 (auxiliary_budget_eq 1) N12Compact.C981DomainSubset.single976_3_1_checked) rfl

def domain3 : CertifiedDomain family := refineQueries corner3
  [⟨N12Compact.C981DomainSubset.query976_249,N12Compact.C981DomainSubset.query976_249_checked⟩,⟨N12Compact.C981DomainSubset.query976_250,N12Compact.C981DomainSubset.query976_250_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_251,N12Compact.C981DomainSubset.query976_251_checked⟩] (by decide)

def corner4 : CertifiedDomain family :=
  .ofDirectProduct _ N12Compact.C981DomainSubset.single976_4_0 N12Compact.C981DomainSubset.single976_4_1
    (direct_check_transport _ _ _ 0 (auxiliary_budget_eq 0) N12Compact.C981DomainSubset.single976_4_0_checked)
    (direct_check_transport _ _ _ 1 (auxiliary_budget_eq 1) N12Compact.C981DomainSubset.single976_4_1_checked) rfl

def domain4 : CertifiedDomain family := refineQueries corner4
  [⟨N12Compact.C981DomainSubset.query976_268,N12Compact.C981DomainSubset.query976_268_checked⟩,⟨N12Compact.C981DomainSubset.query976_269,N12Compact.C981DomainSubset.query976_269_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_270,N12Compact.C981DomainSubset.query976_270_checked⟩] (by decide)

def domain5 : CertifiedDomain family :=
  .ofCombined _ combinedSpec8 combinedSpec8_checked (by decide)

def central6 : CertifiedDomain family :=
  .ofDirectProduct _ N12Compact.C981DomainSubset.single976_7_0 N12Compact.C981DomainSubset.single976_7_1
    (direct_check_transport _ _ _ 0 (auxiliary_budget_eq 0) N12Compact.C981DomainSubset.single976_7_0_checked)
    (direct_check_transport _ _ _ 1 (auxiliary_budget_eq 1) N12Compact.C981DomainSubset.single976_7_1_checked) rfl

def centralQueries : List {q : LocalQuery // q.Check} :=
  [⟨N12Compact.C981DomainSubset.query976_649,N12Compact.C981DomainSubset.query976_649_checked⟩,⟨N12Compact.C981DomainSubset.query976_650,N12Compact.C981DomainSubset.query976_650_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_651,N12Compact.C981DomainSubset.query976_651_checked⟩,⟨N12Compact.C981DomainSubset.query976_652,N12Compact.C981DomainSubset.query976_652_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_653,N12Compact.C981DomainSubset.query976_653_checked⟩,⟨N12Compact.C981DomainSubset.query976_654,N12Compact.C981DomainSubset.query976_654_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_655,N12Compact.C981DomainSubset.query976_655_checked⟩,⟨N12Compact.C981DomainSubset.query976_656,N12Compact.C981DomainSubset.query976_656_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_657,N12Compact.C981DomainSubset.query976_657_checked⟩,⟨N12Compact.C981DomainSubset.query976_658,N12Compact.C981DomainSubset.query976_658_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_659,N12Compact.C981DomainSubset.query976_659_checked⟩,⟨N12Compact.C981DomainSubset.query976_660,N12Compact.C981DomainSubset.query976_660_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_661,N12Compact.C981DomainSubset.query976_661_checked⟩,⟨N12Compact.C981DomainSubset.query976_662,N12Compact.C981DomainSubset.query976_662_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_663,N12Compact.C981DomainSubset.query976_663_checked⟩,⟨N12Compact.C981DomainSubset.query976_664,N12Compact.C981DomainSubset.query976_664_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_665,N12Compact.C981DomainSubset.query976_665_checked⟩,⟨N12Compact.C981DomainSubset.query976_666,N12Compact.C981DomainSubset.query976_666_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_667,N12Compact.C981DomainSubset.query976_667_checked⟩,⟨N12Compact.C981DomainSubset.query976_668,N12Compact.C981DomainSubset.query976_668_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_669,N12Compact.C981DomainSubset.query976_669_checked⟩,⟨N12Compact.C981DomainSubset.query976_670,N12Compact.C981DomainSubset.query976_670_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_671,N12Compact.C981DomainSubset.query976_671_checked⟩,⟨N12Compact.C981DomainSubset.query976_672,N12Compact.C981DomainSubset.query976_672_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_673,N12Compact.C981DomainSubset.query976_673_checked⟩,⟨N12Compact.C981DomainSubset.query976_674,N12Compact.C981DomainSubset.query976_674_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_675,N12Compact.C981DomainSubset.query976_675_checked⟩,⟨N12Compact.C981DomainSubset.query976_676,N12Compact.C981DomainSubset.query976_676_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_677,N12Compact.C981DomainSubset.query976_677_checked⟩,⟨N12Compact.C981DomainSubset.query976_678,N12Compact.C981DomainSubset.query976_678_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_679,N12Compact.C981DomainSubset.query976_679_checked⟩,⟨N12Compact.C981DomainSubset.query976_680,N12Compact.C981DomainSubset.query976_680_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_681,N12Compact.C981DomainSubset.query976_681_checked⟩,⟨N12Compact.C981DomainSubset.query976_682,N12Compact.C981DomainSubset.query976_682_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_683,N12Compact.C981DomainSubset.query976_683_checked⟩,⟨N12Compact.C981DomainSubset.query976_684,N12Compact.C981DomainSubset.query976_684_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_685,N12Compact.C981DomainSubset.query976_685_checked⟩,⟨N12Compact.C981DomainSubset.query976_686,N12Compact.C981DomainSubset.query976_686_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_687,N12Compact.C981DomainSubset.query976_687_checked⟩,⟨N12Compact.C981DomainSubset.query976_688,N12Compact.C981DomainSubset.query976_688_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_689,N12Compact.C981DomainSubset.query976_689_checked⟩,⟨N12Compact.C981DomainSubset.query976_690,N12Compact.C981DomainSubset.query976_690_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_691,N12Compact.C981DomainSubset.query976_691_checked⟩,⟨N12Compact.C981DomainSubset.query976_692,N12Compact.C981DomainSubset.query976_692_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_693,N12Compact.C981DomainSubset.query976_693_checked⟩,⟨N12Compact.C981DomainSubset.query976_694,N12Compact.C981DomainSubset.query976_694_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_695,N12Compact.C981DomainSubset.query976_695_checked⟩,⟨N12Compact.C981DomainSubset.query976_696,N12Compact.C981DomainSubset.query976_696_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_697,N12Compact.C981DomainSubset.query976_697_checked⟩,⟨N12Compact.C981DomainSubset.query976_698,N12Compact.C981DomainSubset.query976_698_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_699,N12Compact.C981DomainSubset.query976_699_checked⟩,⟨N12Compact.C981DomainSubset.query976_700,N12Compact.C981DomainSubset.query976_700_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_701,N12Compact.C981DomainSubset.query976_701_checked⟩,⟨N12Compact.C981DomainSubset.query976_702,N12Compact.C981DomainSubset.query976_702_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_703,N12Compact.C981DomainSubset.query976_703_checked⟩,⟨N12Compact.C981DomainSubset.query976_704,N12Compact.C981DomainSubset.query976_704_checked⟩,
   ⟨N12Compact.C981DomainSubset.query976_705,N12Compact.C981DomainSubset.query976_705_checked⟩]

def domain6 : CertifiedDomain family := refineQueries central6 centralQueries (by decide)

def domain7 : CertifiedDomain family :=
  .ofCombined _ combinedSpec13 combinedSpec13_checked (by decide)

def domain8 : CertifiedDomain family :=
  .ofCombined _ combinedSpec17 combinedSpec17_checked (by decide)

def domain9 : CertifiedDomain family :=
  .ofCombined _ combinedSpec19 combinedSpec19_checked (by decide)

def domain10 : CertifiedDomain family :=
  .ofCombined _ combinedSpec21 combinedSpec21_checked (by decide)

def domain11 : CertifiedDomain family :=
  .ofCombined _ combinedSpec24 combinedSpec24_checked (by decide)

def domains : List (CertifiedDomain family) :=
  [domain0,domain1,domain2,domain3,domain4,domain5,
   domain6,domain7,domain8,domain9,domain10,domain11]

def assignments : List (List (Finset Nat)) :=
  enumerateAssignments (domains.map (fun d => d.allowed)) ∅

/-- Every actual packing has one of the enumerated whole ownership vectors;
no saved row, initial-angle sample, or symmetry assumption supplies coverage. -/
theorem ownership_mem_assignments (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : ownershipVector p ∈ assignments := by
  have h := certified_domain_assignments_mem domains (by decide) (by decide) p hf
  exact h

end
end S12Completion.C981
