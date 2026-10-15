import Compact.Completion.OtherCases.C1090.AuxiliaryCover
import Compact.Completion.FiniteCases.C997Domains

/-! The two small existing combined local certificates needed by C1090.
Their geometry is instantiated at the actual C1090 family and its true
three-exemption budgets. No C997 family theorem or reported C1090 catalogue
is a premise. Complete owned sets and extra ownership are retained. The
existing numerical certificate trust is inherited, with no new native site.
Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1090.DirectDomains
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

end
#print axioms right_points
#print axioms top_component
end N12Compact.Completion.OtherCases.C1090.DirectDomains
