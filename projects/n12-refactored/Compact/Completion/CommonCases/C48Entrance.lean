import Compact.Completion.CommonCases.OriginalOwners
import S12.DomainSpecData

/-! The actual C48/C573/C574 entrance. Each ordinary domain is cached
only after the real F3/G2 budget. Single-owner cuts propagate the strict
pairs; no Cartesian ownership search or auxiliary claim about the paired
corner owners is required. -/
namespace N12Compact.CommonCases.C48Rows
open S12 S12Pilot OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

inductive Kind where
  | c48 | c573 | c574
  deriving DecidableEq

def bottom : Kind → Nat
  | .c48 => 4
  | .c573 => 8192
  | .c574 => 8196

def family : Kind → Finset Nat
  | .c48 => {1,2,4,8,48,192,256,1536,2048,4096,16384,32768}
  | .c573 => {1,2,8,48,192,256,1536,2048,4096,8192,16384,32768}
  | .c574 => {1,2,8,48,192,256,1536,2048,4096,8196,16384,32768}

private theorem budget_counts (k : Kind) : (family k∩auxExempt 0).card=3 ∧
    (family k∩auxExempt 1).card=2 := by cases k <;> decide +kernel

private def direct (k : Kind) (w : CombinedSpec) (hw : w.Check)
    (hF : Bounds (family k) w.mask w.first.val 0)
    (hG : Bounds (family k) w.mask w.second.val 1)
    (fNon : w.mask∉auxExempt 0) (gNon : w.mask∉auxExempt 1) : CertifiedDomain (family k) :=
  restrict_budget23 (family k) (ofCombined (family k) w hw hF hG)
    (budget_counts k).1 (budget_counts k).2 fNon gNon

private def southAllowed : List (Finset Nat) := [{0,10},{0,12},{0,13},{2,10},{2,12},{2,13},{4,10},{4,12},{4,13},{0,1,13},{0,2,10},{0,2,12},{0,2,13},{0,4,10},{0,4,12},{0,4,13},{0,5,13},{1,4,13},{2,4,10},{2,4,12},{2,4,13},{4,5,13}]
private def southDomain (k : Kind) : CertifiedDomain (family k) :=
  cached_domain (family k)
    (direct k combinedSpec6 combinedSpec6_checked
      (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    256 southAllowed rfl rfl

private def bottomAllowed : List (Finset Nat) := [{2,12},{6,15},{2,4,12},{4,6,15}]
private def bottomDomain (k : Kind) : CertifiedDomain (family k) :=
  cached_domain (family k)
    (direct k combinedSpec19 combinedSpec19_checked
      (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    8192 bottomAllowed rfl rfl

private def rightAllowed : List (Finset Nat) := [{8,18},{9,19},{6,8,18},{7,9,19},{8,9,18},{8,9,19}]
private def rightDomain (k : Kind) : CertifiedDomain (family k) :=
  cached_domain (family k)
    (direct k combinedSpec21 combinedSpec21_checked
      (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    16384 rightAllowed rfl rfl

private def topAllowed : List (Finset Nat) := [{3,14},{7,17},{3,5,14},{5,7,17}]
private def topDomain (k : Kind) : CertifiedDomain (family k) :=
  cached_domain (family k)
    (direct k combinedSpec24 combinedSpec24_checked
      (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    32768 topAllowed rfl rfl

private def northAllowed : List (Finset Nat) := [{1,11},{1,13},{1,14},{3,11},{3,13},{3,14},{5,11},{5,13},{5,14},{0,1,13},{0,5,13},{1,3,11},{1,3,13},{1,3,14},{1,4,13},{1,5,11},{1,5,13},{1,5,14},{3,5,11},{3,5,13},{3,5,14},{4,5,13}]
private def northDomain (k : Kind) : CertifiedDomain (family k) :=
  cached_domain (family k)
    (direct k combinedSpec13 combinedSpec13_checked
      (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    2048 northAllowed rfl rfl

private def leftAllowed : List (Finset Nat) := [{0,10},{1,11},{0,1,10},{0,1,11},{0,2,10},{1,3,11}]
private def leftDomain (k : Kind) : CertifiedDomain (family k) :=
  cached_domain (family k)
    (direct k combinedSpec17 combinedSpec17_checked
      (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) (by decide +kernel))
    4096 leftAllowed rfl rfl

private theorem south_checked : ∀ a∈southAllowed,
    Disjoint a ({0,10} : Finset Nat) → Disjoint a ({2,12} : Finset Nat) →
    ({4,13} : Finset Nat)⊆a := by decide +kernel
private theorem bottom_checked : ∀ a∈bottomAllowed,
    Disjoint a ({2,12} : Finset Nat) → ({6,15} : Finset Nat)⊆a := by decide +kernel
private theorem left_checked : ∀ a∈leftAllowed,
    Disjoint a ({0,10} : Finset Nat) → ({1,11} : Finset Nat)⊆a := by decide +kernel
private theorem right_checked : ∀ a∈rightAllowed,
    Disjoint a ({8,18} : Finset Nat) → Disjoint a ({6,15} : Finset Nat) →
    ({9,19} : Finset Nat)⊆a := by decide +kernel
private theorem north_checked : ∀ a∈northAllowed,
    Disjoint a ({1,11} : Finset Nat) → Disjoint a ({4,13} : Finset Nat) → 14∈a := by decide +kernel
private theorem top_checked : ∀ a∈topAllowed, 14∉a → ({7,17} : Finset Nat)⊆a := by decide +kernel
private theorem north_outward_checked : ∀ a∈northAllowed,
    Disjoint a ({1,11} : Finset Nat) → Disjoint a ({4,13} : Finset Nat) →
    5∉a → ({3,14} : Finset Nat)⊆a := by decide +kernel

theorem seed_point (k : Kind) (p : NormalizedPacking) (hf : codedMarkerFamily p=family k)
    (mask : Nat) (member : mask∈family k) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed (family k) p hf mask member P checked

theorem auxiliary_point (p : NormalizedPacking) (mask : Nat) (owned : Finset Nat)
    (sub : owned⊆auxiliaries p mask) (j : Nat) (bound : j<20) (member : j∈owned) :
    (owner p mask).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 :=
  (auxiliary_exact p mask j bound).mpr (sub member)

theorem pair_from_points (p : NormalizedPacking) (mask a b : Nat) (aBound : a<20) (bBound : b<20)
    (first : (owner p mask).Inside ((auxPoints 2)[a]!).1 ((auxPoints 2)[a]!).2)
    (second : (owner p mask).Inside ((auxPoints 2)[b]!).1 ((auxPoints 2)[b]!).2) :
    ({a,b} : Finset Nat)⊆auxiliaries p mask := by
  intro j hj
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with ha | hb
  · rw [ha]
    exact (auxiliary_exact p mask a aBound).mp first
  · rw [hb]
    exact (auxiliary_exact p mask b bBound).mp second

structure BasePairs (k : Kind) (p : NormalizedPacking) : Prop where
  bottomSingleton : ({2,12} : Finset Nat)⊆auxiliaries p 1
  leftSingleton : ({0,10} : Finset Nat)⊆auxiliaries p 2
  rightSingleton : ({8,18} : Finset Nat)⊆auxiliaries p 8
  bottomWall : ({6,15} : Finset Nat)⊆auxiliaries p (bottom k)
  southwest : ({4,13} : Finset Nat)⊆auxiliaries p 256
  leftWall : ({1,11} : Finset Nat)⊆auxiliaries p 4096
  rightWall : ({9,19} : Finset Nat)⊆auxiliaries p 16384
  topWall : ({7,17} : Finset Nat)⊆auxiliaries p 32768
  northwest : 14∈auxiliaries p 2048

theorem entrance (k : Kind) (p : NormalizedPacking) (hf : codedMarkerFamily p=family k) :
    BasePairs k p := by
  have oLow : (owner p 1).Inside (28/25) 1 := by
    have h := seed_point k p hf 1 (by cases k <;> decide +kernel) (28/25,1) (by decide +kernel)
    norm_num at h; exact h
  have oHigh : (owner p 1).Inside (87/50) 1 := by
    have h := seed_point k p hf 1 (by cases k <;> decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have oF : (owner p 1).Inside (8/5) 1 :=
    horizontal_segment _ _ _ _ _ oLow oHigh (by norm_num) (by norm_num) (by norm_num)
  have vLow : (owner p 2).Inside 1 (28/25) := by
    have h := seed_point k p hf 2 (by cases k <;> decide +kernel) (1,28/25) (by decide +kernel)
    norm_num at h; exact h
  have vHigh : (owner p 2).Inside 1 (87/50) := by
    have h := seed_point k p hf 2 (by cases k <;> decide +kernel) (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  have vG : (owner p 2).Inside 1 (8/5) :=
    vertical_segment _ _ _ _ _ vLow vHigh (by norm_num) (by norm_num) (by norm_num)
  have iLow : (owner p 8).Inside 3 (28/25) := by
    have h := seed_point k p hf 8 (by cases k <;> decide +kernel) (3,28/25) (by decide +kernel)
    norm_num at h; exact h
  have iHigh : (owner p 8).Inside 3 (87/50) := by
    have h := seed_point k p hf 8 (by cases k <;> decide +kernel) (3,87/50) (by decide +kernel)
    norm_num at h; exact h
  have iG : (owner p 8).Inside 3 (8/5) :=
    vertical_segment _ _ _ _ _ iLow iHigh (by norm_num) (by norm_num) (by norm_num)
  have o := pair_from_points p 1 2 12 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact oF)
    (by norm_num [auxPoints,fPoints,gPoints]; exact oHigh)
  have v := pair_from_points p 2 0 10 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact vHigh)
    (by norm_num [auxPoints,fPoints,gPoints]; exact vG)
  have i := pair_from_points p 8 8 18 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact iHigh)
    (by norm_num [auxPoints,fPoints,gPoints]; exact iG)
  have b : ({6,15} : Finset Nat)⊆auxiliaries p (bottom k) := by
    cases k
    · have lo : (owner p 4).Inside (113/50) 1 := by
        have h := seed_point .c48 p hf 4 (by decide +kernel) (113/50,1) (by decide +kernel)
        norm_num at h; exact h
      have hi : (owner p 4).Inside (72/25) 1 := by
        have h := seed_point .c48 p hf 4 (by decide +kernel) (72/25,1) (by decide +kernel)
        norm_num at h; exact h
      exact pair_from_points p 4 6 15 (by norm_num) (by norm_num)
        (by norm_num [auxPoints,fPoints,gPoints]; exact
          horizontal_segment _ _ _ _ _ lo hi (by norm_num) (by norm_num) (by norm_num))
        (by norm_num [auxPoints,fPoints,gPoints]; exact lo)
    · have apartO := auxiliary_disjoint (family .c573) p hf 8192 1
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
      exact bottom_checked _ (domain (family .c573) (bottomDomain .c573) p hf (by decide +kernel))
        (apartO.mono_right o)
    · have lo : (owner p 8196).Inside (9/4) 1 := by
        have h := seed_point .c574 p hf 8196 (by decide +kernel) (9/4,1) (by decide +kernel)
        norm_num at h; exact h
      have hi : (owner p 8196).Inside (11/4) 1 := by
        have h := seed_point .c574 p hf 8196 (by decide +kernel) (11/4,1) (by decide +kernel)
        norm_num at h; exact h
      exact pair_from_points p 8196 6 15 (by norm_num) (by norm_num)
        (by norm_num [auxPoints,fPoints,gPoints]; exact
          horizontal_segment _ _ _ _ _ lo hi (by norm_num) (by norm_num) (by norm_num))
        (by norm_num [auxPoints,fPoints,gPoints]; exact
          horizontal_segment _ _ _ _ _ lo hi (by norm_num) (by norm_num) (by norm_num))
  have aV := auxiliary_disjoint (family k) p hf 256 2
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have aO := auxiliary_disjoint (family k) p hf 256 1
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have a := south_checked _ (domain (family k) (southDomain k) p hf (by cases k <;> decide +kernel))
    (aV.mono_right v) (aO.mono_right o)
  have lV := auxiliary_disjoint (family k) p hf 4096 2
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have l := left_checked _ (domain (family k) (leftDomain k) p hf (by cases k <;> decide +kernel))
    (lV.mono_right v)
  have rI := auxiliary_disjoint (family k) p hf 16384 8
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have rB := auxiliary_disjoint (family k) p hf 16384 (bottom k)
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
    (by cases k <;> decide +kernel)
  have r := right_checked _ (domain (family k) (rightDomain k) p hf (by cases k <;> decide +kernel))
    (rI.mono_right i) (rB.mono_right b)
  have nL := auxiliary_disjoint (family k) p hf 2048 4096
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have nA := auxiliary_disjoint (family k) p hf 2048 256
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have n := north_checked _ (domain (family k) (northDomain k) p hf (by cases k <;> decide +kernel))
    (nL.mono_right l) (nA.mono_right a)
  have tN := auxiliary_disjoint (family k) p hf 32768 2048
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have t := top_checked _ (domain (family k) (topDomain k) p hf (by cases k <;> decide +kernel))
    (fun h => Finset.disjoint_left.mp tN h n)
  exact ⟨o,v,i,b,a,l,r,t,n⟩

theorem north_outward (k : Kind) (p : NormalizedPacking) (hf : codedMarkerFamily p=family k)
    (pairs : BasePairs k p) (wInward : (owner p 1536).Inside 2 (113/50)) :
    ({3,14} : Finset Nat)⊆auxiliaries p 2048 := by
  have nL := auxiliary_disjoint (family k) p hf 2048 4096
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have nA := auxiliary_disjoint (family k) p hf 2048 256
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have nW := auxiliary_disjoint (family k) p hf 2048 1536
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel)
  have w : 5∈auxiliaries p 1536 := by
    apply (auxiliary_exact p 1536 5 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]; exact wInward
  exact north_outward_checked _ (domain (family k) (northDomain k) p hf (by cases k <;> decide +kernel))
    (nL.mono_right pairs.leftWall) (nA.mono_right pairs.southwest)
    (fun h => Finset.disjoint_left.mp nW h w)

#print axioms entrance
end
end N12Compact.CommonCases.C48Rows
