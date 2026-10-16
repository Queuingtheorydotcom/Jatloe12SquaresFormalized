import Compact.Completion.FiniteCases.C896Domains
import Mathlib.Tactic.IntervalCases

/-! Compulsory points of the original C896 family. The three singleton
segments are obtained from their actual marker signatures, including the
half-turn singleton with mask 16. The F count is one for ordinary owners;
no G cardinality or complete G label is strengthened here. -/
namespace N12Compact.FiniteCases.C896Entrance
open S12 S12Pilot C896Domains
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

structure Compulsory (p : NormalizedPacking) : Prop where
  southwest : 2∈auxiliaries p 1 ∧ 12∈auxiliaries p 1
  leftSingleton : 0∈auxiliaries p 2 ∧ 10∈auxiliaries p 2
  northeastSingleton : 7∈auxiliaries p 16 ∧ 17∈auxiliaries p 16
  bottom : 6∈auxiliaries p 8192 ∧ 15∈auxiliaries p 8192
  leftWall : 1∈auxiliaries p 4096 ∧ 11∈auxiliaries p 4096
  top : 3∈auxiliaries p 32768 ∧ 14∈auxiliaries p 32768
  northwest : 5∈auxiliaries p 2048 ∧ 13∈auxiliaries p 2048
  northeast : 9∈auxiliaries p 1024
  rightWall : 8∈auxiliaries p 16384 ∧ 18∈auxiliaries p 16384
  merged : 4∈auxiliaries p 768

private theorem f_combined (p : NormalizedPacking) (mask index : Nat) (bound : index<10) :
    index∈natAuxOwners p 0 (ownerIndex p mask) ↔ index∈auxiliaries p mask := by
  unfold auxiliaries natCombinedOwners
  exact (mem_combined_low _ _ index bound).symm

theorem ordinary_f_card (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (non : mask∉auxExempt 0) :
    (natAuxOwners p 0 (ownerIndex p mask)).card=1 := by
  have budget := nat_aux_budget p 0 (ownerIndex p mask)
  have count : (family∩auxExempt 0).card=2 := by decide +kernel
  rw [hf,code _ p hf mask member,count] at budget
  simp only [non,ite_false] at budget
  omega

private theorem singleton_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) :
    (2∈auxiliaries p 1 ∧ 12∈auxiliaries p 1) ∧
      (0∈auxiliaries p 2 ∧ 10∈auxiliaries p 2) ∧
      (7∈auxiliaries p 16 ∧ 17∈auxiliaries p 16) := by
  have swNear : (owner p 1).Inside (28/25) 1 := by
    have h := seed _ p hf 1 (by decide +kernel) ((28/25,1) : ℚ×ℚ)
      (by decide +kernel)
    norm_num at h; exact h
  have swFar : (owner p 1).Inside (87/50) 1 := by
    have h := seed _ p hf 1 (by decide +kernel) ((87/50,1) : ℚ×ℚ)
      (by decide +kernel)
    norm_num at h; exact h
  have swMid : (owner p 1).Inside (8/5) 1 :=
    horizontal_segment _ _ _ _ _ swNear swFar (by norm_num) (by norm_num) (by norm_num)
  have leftNear : (owner p 2).Inside 1 (28/25) := by
    have h := seed _ p hf 2 (by decide +kernel) ((1,28/25) : ℚ×ℚ)
      (by decide +kernel)
    norm_num at h; exact h
  have leftFar : (owner p 2).Inside 1 (87/50) := by
    have h := seed _ p hf 2 (by decide +kernel) ((1,87/50) : ℚ×ℚ)
      (by decide +kernel)
    norm_num at h; exact h
  have leftMid : (owner p 2).Inside 1 (8/5) :=
    vertical_segment _ _ _ _ _ leftNear leftFar (by norm_num) (by norm_num) (by norm_num)
  -- Half-turn images of (1.74,1) and (1.12,1), in increasing x order.
  have neFar : (owner p 16).Inside (113/50) 3 := by
    have h := seed _ p hf 16 (by decide +kernel) ((113/50,3) : ℚ×ℚ)
      (by decide +kernel)
    norm_num at h; exact h
  have neNear : (owner p 16).Inside (72/25) 3 := by
    have h := seed _ p hf 16 (by decide +kernel) ((72/25,3) : ℚ×ℚ)
      (by decide +kernel)
    norm_num at h; exact h
  have neMid : (owner p 16).Inside (12/5) 3 :=
    horizontal_segment _ _ _ _ _ neFar neNear (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · apply (auxiliary_exact p 1 2 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using swMid
  · apply (auxiliary_exact p 1 12 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using swFar
  · apply (auxiliary_exact p 2 0 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using leftFar
  · apply (auxiliary_exact p 2 10 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using leftMid
  · apply (auxiliary_exact p 16 7 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using neMid
  · apply (auxiliary_exact p 16 17 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using neFar

private theorem northeast_cut : ∀ s∈([{5},{7},{9}] : List (Finset Nat)),
    5∉s → 7∉s → 9∈s := by decide +kernel

theorem compulsory (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Compulsory p := by
  have foreign (m n index : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
      (owned : index∈auxiliaries p n) : index∉auxiliaries p m :=
    fun h => Finset.disjoint_left.mp (auxiliary_disjoint _ p hf m n hm hn different) h owned
  obtain ⟨sw,low,neSingleton⟩ := singleton_points p hf
  have bottom := bottom_forced _ (domain _ C896Domains.bottom p hf (by decide +kernel))
    (foreign 8192 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) sw.1)
  have left := left_forced _ (domain _ C896Domains.left p hf (by decide +kernel))
    (foreign 4096 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) low.1)
  have top := top_forced _ (domain _ C896Domains.top p hf (by decide +kernel))
    (foreign 32768 16 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) neSingleton.1)
  have nw := northwest_forced _ (domain _ C896Domains.northwest p hf (by decide +kernel))
    (foreign 2048 4096 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) left.1)
    (foreign 2048 32768 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) top.1)
    (foreign 2048 4096 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) left.2)
    (foreign 2048 32768 14 (by decide +kernel) (by decide +kernel) (by decide +kernel) top.2)
  have ne : 9∈auxiliaries p 1024 := by
    have allowed := northeastF.sound p _ hf (code _ p hf 1024 (by decide +kernel))
    apply (f_combined p 1024 9 (by decide +kernel)).mp
    apply northeast_cut _ allowed
    · intro own
      exact foreign 1024 2048 5 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) nw.1 ((f_combined p 1024 5 (by decide +kernel)).mp own)
    · intro own
      exact foreign 1024 16 7 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) neSingleton.1 ((f_combined p 1024 7 (by decide +kernel)).mp own)
  have right := right_forced _ (domain _ C896Domains.right p hf (by decide +kernel))
    (foreign 16384 1024 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) ne)
  have merged : 4∈auxiliaries p 768 := by
    have card := ordinary_f_card p hf 768 (by decide +kernel) (by decide +kernel)
    obtain ⟨j,hj⟩ := Finset.card_pos.mp (show 0<(natAuxOwners p 0 (ownerIndex p 768)).card by omega)
    have bound := Finset.mem_range.mp (nat_aux_subset p 0 _ hj)
    have own := (f_combined p 768 j bound).mp hj
    interval_cases j
    · exact False.elim (foreign 768 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel) low.1 own)
    · exact False.elim (foreign 768 4096 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) left.1 own)
    · exact False.elim (foreign 768 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) sw.1 own)
    · exact False.elim (foreign 768 32768 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) top.1 own)
    · exact own
    · exact False.elim (foreign 768 2048 5 (by decide +kernel) (by decide +kernel) (by decide +kernel) nw.1 own)
    · exact False.elim (foreign 768 8192 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) bottom.1 own)
    · exact False.elim (foreign 768 16 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) neSingleton.1 own)
    · exact False.elim (foreign 768 16384 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) right.1 own)
    · exact False.elim (foreign 768 1024 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) ne own)
  exact ⟨sw,low,neSingleton,bottom,left,top,nw,ne,right,merged⟩

#print axioms compulsory
end
end N12Compact.FiniteCases.C896Entrance
