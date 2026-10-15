import Compact.Completion.FiniteCases.C997FiniteCuts

/-! An acyclic compulsory-point chain for the original C997 packing.
The original two-F and two-G allowances are retained. Each deletion is
justified by a concrete point strictly owned by one different square. -/
namespace N12Compact.FiniteCases.C997Points
open S12 S12Pilot RelaxedOwnerDomain C997Entrance C997Domains
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

private theorem absent (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n index : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
    (owned : index∈auxiliaries p n) : index∉auxiliaries p m :=
  fun h => Finset.disjoint_left.mp
    (auxiliary_disjoint _ p hf m n hm hn different) h owned

/-- These are memberships of the complete actual twenty-point labels,
not hypothesized selected rows or bounds on the two central angles. -/
theorem compulsory (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (6∈auxiliaries p 8192 ∧ 15∈auxiliaries p 8192) ∧
      (7∈auxiliaries p 32768 ∧ 17∈auxiliaries p 32768) ∧
      (8∈auxiliaries p 512 ∧ 18∈auxiliaries p 512) ∧
      (9∈auxiliaries p 16384 ∧ 19∈auxiliaries p 16384) ∧
      (5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024) := by
  have sw : 2∈auxiliaries p 1 := by
    have h := domain _ southwest p hf (by decide +kernel)
    exact C997FiniteCuts.southwest_has_two _ h
  have low : 0∈auxiliaries p 2 := by
    apply (auxiliary_exact p 2 0 (by decide +kernel)).mp
    have h := seed _ p hf 2 (by decide +kernel) ((1,87/50) : ℚ×ℚ) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h ⊢
    exact h
  have bottomPoints : 6∈auxiliaries p 8192 ∧ 15∈auxiliaries p 8192 := by
    have h := domain _ bottom p hf (by decide +kernel)
    have no2 := absent p hf 8192 1 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) sw
    exact C997FiniteCuts.bottom_points _ h no2
  have swCentral : 4∈auxiliaries p 256 := by
    have h := domain _ southwestCentral p hf (by decide +kernel)
    have no0 := absent p hf 256 2 0 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) low
    have no2 := absent p hf 256 1 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) sw
    have no6 := absent p hf 256 8192 6 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) bottomPoints.1
    exact C997FiniteCuts.southwest_has_four _ h no0 no2 no6
  have merged : 3∈auxiliaries p 2240 := by
    apply (auxiliary_exact p 2240 3 (by decide +kernel)).mp
    simpa [auxPoints,fPoints,gPoints] using merged_outward p hf
  have topPoints : 7∈auxiliaries p 32768 ∧ 17∈auxiliaries p 32768 := by
    have h := domain _ top p hf (by decide +kernel)
    have no3 := absent p hf 32768 2240 3 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) merged
    exact C997FiniteCuts.top_points _ h no3
  have seF : 8∈auxiliaries p 512 := by
    have h := domain _ southeast p hf (by decide +kernel)
    have no4 := absent p hf 512 256 4 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) swCentral
    have no6 := absent p hf 512 8192 6 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) bottomPoints.1
    exact C997FiniteCuts.southeast_has_eight _ h no4 no6
  have rightPoints : 9∈auxiliaries p 16384 ∧ 19∈auxiliaries p 16384 := by
    have h := domain _ right p hf (by decide +kernel)
    have no8 := absent p hf 16384 512 8 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) seF
    have no7 := absent p hf 16384 32768 7 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) topPoints.1
    exact C997FiniteCuts.right_points _ h no8 no7
  have nePoints : 5∈auxiliaries p 1024 ∧ 16∈auxiliaries p 1024 := by
    have h := domain _ northeast p hf (by decide +kernel)
    have no7 := absent p hf 1024 32768 7 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) topPoints.1
    have no9 := absent p hf 1024 16384 9 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rightPoints.1
    have no17 := absent p hf 1024 32768 17 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) topPoints.2
    have no19 := absent p hf 1024 16384 19 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) rightPoints.2
    exact C997FiniteCuts.northeast_points _ h no7 no9 no17 no19
  have seG : 18∈auxiliaries p 512 := by
    have h := domain _ southeast p hf (by decide +kernel)
    have no15 := absent p hf 512 8192 15 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) bottomPoints.2
    have no16 := absent p hf 512 1024 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) nePoints.2
    exact C997FiniteCuts.southeast_has_eighteen _ h no15 no16
  exact ⟨bottomPoints,topPoints,⟨seF,seG⟩,rightPoints,nePoints⟩

theorem auxiliary_inside (p : NormalizedPacking) (mask index : Nat) (bound : index<20)
    (owned : index∈auxiliaries p mask) :
    (owner p mask).Inside ((auxPoints 2)[index]!).1 ((auxPoints 2)[index]!).2 :=
  (auxiliary_exact p mask index bound).mpr owned

#print axioms compulsory
end
end N12Compact.FiniteCases.C997Points
