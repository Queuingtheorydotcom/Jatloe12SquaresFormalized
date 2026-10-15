import Compact.Completion.OtherCases.C1089.AuxiliaryCover
import Compact.Completion.FiniteCases.C997Domains

/-! Four existing small combined local certificates on the actual C1089 family.
Their geometry is instantiated at the actual C1089 family and its true
three-exemption budgets. No C997 family theorem or reported C1089 catalogue
is a premise. Complete owned sets and extra ownership are retained. The
existing numerical certificate trust is inherited, with no new native site.
Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.DirectDomains
open S12 S12Pilot RelaxedOwnerDomain OriginalData
set_option Elab.async false
noncomputable section

private theorem bounds (mask : Nat) (w : SingleSpec) (k : Fin 2)
    (low : w.lower=1) (high : w.upper=2) (non : mask∉auxExempt k) :
    Bounds family mask w k := by
  unfold Bounds upper lower
  rw [low,high,AuxiliaryCover.exemption_count k]
  simp only [non,if_false]
  norm_num

def leftAllowed : List (Finset Nat) :=
  [{0,10},{0,10,13},{1,11},{1,11,13},{0,1,10},{0,1,11},
   {0,1,10,11},{0,1,10,13},{0,1,11,13},{0,2,10},{1,3,11}]

def left : CertifiedDomain family :=
  CommonCases.OriginalOwners.cached_domain _
    (ofCombined _ combinedSpec17 combinedSpec17_checked
      (bounds _ _ 0 rfl rfl (by decide +kernel))
      (bounds _ _ 1 rfl rfl (by decide +kernel)))
    4096 leftAllowed rfl rfl

def bottom : CertifiedDomain family :=
  CommonCases.OriginalOwners.cached_domain _
    (ofCombined _ combinedSpec19 combinedSpec19_checked
      (bounds _ _ 0 rfl rfl (by decide +kernel))
      (bounds _ _ 1 rfl rfl (by decide +kernel)))
    8192 FiniteCases.C997Domains.bottomAllowed rfl rfl

def right : CertifiedDomain family :=
  CommonCases.OriginalOwners.cached_domain _
    (ofCombined _ combinedSpec21 combinedSpec21_checked
      (bounds _ _ 0 rfl rfl (by decide +kernel))
      (bounds _ _ 1 rfl rfl (by decide +kernel)))
    16384 FiniteCases.C997Domains.rightAllowed rfl rfl

def top : CertifiedDomain family :=
  CommonCases.OriginalOwners.cached_domain _
    (ofCombined _ combinedSpec24 combinedSpec24_checked
      (bounds _ _ 0 rfl rfl (by decide +kernel))
      (bounds _ _ 1 rfl rfl (by decide +kernel)))
    32768 FiniteCases.C997Domains.topAllowed rfl rfl

private theorem right_cut : ∀ owned∈FiniteCases.C997Domains.rightAllowed,
    8∉owned → 9∈owned ∧ 19∈owned := by decide +kernel

private theorem top_cut : ∀ owned∈FiniteCases.C997Domains.topAllowed,
    17∈owned ∨ (3∈owned ∧ 14∈owned) := by decide +kernel

theorem right_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : 8∉CommonCases.OriginalOwners.auxiliaries p 16384) :
    (owners p 10).Inside 3 (113/50) ∧ (owners p 10).Inside 3 (12/5) := by
  have member := CommonCases.OriginalOwners.domain family right p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 16384∈
    FiniteCases.C997Domains.rightAllowed at member
  have pair := right_cut _ member missing
  have first := (CommonCases.OriginalOwners.auxiliary_exact p 16384 9 (by norm_num)).mpr pair.1
  have second := (CommonCases.OriginalOwners.auxiliary_exact p 16384 19 (by norm_num)).mpr pair.2
  exact ⟨by simpa [owners,masks,auxPoints,fPoints,gPoints] using first,
    by simpa [owners,masks,auxPoints,fPoints,gPoints] using second⟩

theorem top_component (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (113/50) 3 ∨
      ((owners p 11).Inside (8/5) 3 ∧ (owners p 11).Inside (87/50) 3) := by
  have member := CommonCases.OriginalOwners.domain family top p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 32768∈
    FiniteCases.C997Domains.topAllowed at member
  rcases top_cut _ member with own | pair
  · left
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 32768 17 (by norm_num)).mpr own
    simpa [owners,masks,auxPoints,fPoints,gPoints] using point
  · right
    have first := (CommonCases.OriginalOwners.auxiliary_exact p 32768 3 (by norm_num)).mpr pair.1
    have second := (CommonCases.OriginalOwners.auxiliary_exact p 32768 14 (by norm_num)).mpr pair.2
    exact ⟨by simpa [owners,masks,auxPoints,fPoints,gPoints] using first,
      by simpa [owners,masks,auxPoints,fPoints,gPoints] using second⟩

/-- The missing G2 comes from the true singleton, so F6 is compulsory
without any central or wall-center premise. -/
theorem bottom_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (12/5) 1 := by
  have member := CommonCases.OriginalOwners.domain family bottom p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 8192∈
    FiniteCases.C997Domains.bottomAllowed at member
  have omitted : 12∉CommonCases.OriginalOwners.auxiliaries p 8192 := by
    intro own
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 8192 12 (by norm_num)).mpr own
    have far := (frame p hf).singletonFar
    apply (frame p hf).apart 9 0 (by decide) _ _ ⟨?_,far⟩
    simpa [owners,masks,auxPoints,fPoints,gPoints] using point
  have cut : ∀ row∈FiniteCases.C997Domains.bottomAllowed,12∉row → 6∈row := by
    decide +kernel
  have point := (CommonCases.OriginalOwners.auxiliary_exact p 8192 6 (by norm_num)).mpr
    (cut _ member omitted)
  simpa [owners,masks,auxPoints,fPoints,gPoints] using point

theorem left_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 8).Inside 1 (87/50)) :
    (owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5) := by
  have member := CommonCases.OriginalOwners.domain family left p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 4096∈leftAllowed at member
  have absent : 0∉CommonCases.OriginalOwners.auxiliaries p 4096 := by
    intro own
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 4096 0 (by norm_num)).mpr own
    exact missing (by simpa [owners,masks,auxPoints,fPoints,gPoints] using point)
  have cut : ∀ row∈leftAllowed,0∉row → 1∈row ∧ 11∈row := by decide +kernel
  have pair := cut _ member absent
  have a := (CommonCases.OriginalOwners.auxiliary_exact p 4096 1 (by norm_num)).mpr pair.1
  have b := (CommonCases.OriginalOwners.auxiliary_exact p 4096 11 (by norm_num)).mpr pair.2
  exact ⟨by simpa [owners,masks,auxPoints,fPoints,gPoints] using a,
    by simpa [owners,masks,auxPoints,fPoints,gPoints] using b⟩

theorem right_low_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 10).Inside 3 (113/50)) :
    (owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5) := by
  have member := CommonCases.OriginalOwners.domain family right p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 16384∈
    FiniteCases.C997Domains.rightAllowed at member
  have absent : 9∉CommonCases.OriginalOwners.auxiliaries p 16384 := by
    intro own
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 16384 9 (by norm_num)).mpr own
    exact missing (by simpa [owners,masks,auxPoints,fPoints,gPoints] using point)
  have cut : ∀ row∈FiniteCases.C997Domains.rightAllowed,9∉row → 8∈row ∧ 18∈row := by
    decide +kernel
  have pair := cut _ member absent
  have a := (CommonCases.OriginalOwners.auxiliary_exact p 16384 8 (by norm_num)).mpr pair.1
  have b := (CommonCases.OriginalOwners.auxiliary_exact p 16384 18 (by norm_num)).mpr pair.2
  exact ⟨by simpa [owners,masks,auxPoints,fPoints,gPoints] using a,
    by simpa [owners,masks,auxPoints,fPoints,gPoints] using b⟩

theorem right_high_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 10).Inside 3 (87/50)) :
    (owners p 10).Inside 3 (113/50) ∧ (owners p 10).Inside 3 (12/5) := by
  apply right_points p hf
  intro own
  have point := (CommonCases.OriginalOwners.auxiliary_exact p 16384 8 (by norm_num)).mpr own
  exact missing (by simpa [owners,masks,auxPoints,fPoints,gPoints] using point)

theorem top_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (87/50) 3 ∨ (owners p 11).Inside (113/50) 3 := by
  have member := CommonCases.OriginalOwners.domain family top p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 32768∈
    FiniteCases.C997Domains.topAllowed at member
  have cut : ∀ row∈FiniteCases.C997Domains.topAllowed,14∈row ∨ 17∈row := by decide +kernel
  rcases cut _ member with own | own
  · left
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 32768 14 (by norm_num)).mpr own
    simpa [owners,masks,auxPoints,fPoints,gPoints] using point
  · right
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 32768 17 (by norm_num)).mpr own
    simpa [owners,masks,auxPoints,fPoints,gPoints] using point

theorem top_f7 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 11).Inside (8/5) 3) : (owners p 11).Inside (12/5) 3 := by
  have member := CommonCases.OriginalOwners.domain family top p hf (by decide +kernel)
  change CommonCases.OriginalOwners.auxiliaries p 32768∈
    FiniteCases.C997Domains.topAllowed at member
  have absent : 3∉CommonCases.OriginalOwners.auxiliaries p 32768 := by
    intro own
    have point := (CommonCases.OriginalOwners.auxiliary_exact p 32768 3 (by norm_num)).mpr own
    exact missing (by simpa [owners,masks,auxPoints,fPoints,gPoints] using point)
  have cut : ∀ row∈FiniteCases.C997Domains.topAllowed,3∉row → 7∈row := by decide +kernel
  have point := (CommonCases.OriginalOwners.auxiliary_exact p 32768 7 (by norm_num)).mpr
    (cut _ member absent)
  simpa [owners,masks,auxPoints,fPoints,gPoints] using point

end
#print axioms right_points
#print axioms top_component
end N12Compact.Completion.OtherCases.C1089.DirectDomains
