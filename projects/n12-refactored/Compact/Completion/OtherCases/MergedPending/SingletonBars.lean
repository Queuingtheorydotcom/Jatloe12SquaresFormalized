import Compact.Completion.CommonCases.OriginalOwners

/-! Actual singleton segments used by the three pending merged families
C683, C700 and C867. Each closed parameter interval lies strictly inside
one named physical square. Only the corresponding exact singleton mask
is a premise; no auxiliary-domain or packing-symmetry assumption is used.
Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

theorem singleton_bottom (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 1∈family) :
    ∀ x : ℝ,28/25≤x → x≤87/50 → (owner p 1).Inside x 1 := by
  have a := seed family p hf 1 member (28/25,1) (by decide +kernel)
  have b := seed family p hf 1 member (87/50,1) (by decide +kernel)
  norm_num at a b
  exact fun x low high => horizontal_segment _ _ _ _ _ a b (by norm_num) low high

theorem singleton_left (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 2∈family) :
    ∀ y : ℝ,28/25≤y → y≤87/50 → (owner p 2).Inside 1 y := by
  have a := seed family p hf 2 member (1,28/25) (by decide +kernel)
  have b := seed family p hf 2 member (1,87/50) (by decide +kernel)
  norm_num at a b
  exact fun y low high => vertical_segment _ _ _ _ _ a b (by norm_num) low high

theorem singleton_top (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 16∈family) :
    ∀ x : ℝ,113/50≤x → x≤72/25 → (owner p 16).Inside x 3 := by
  have a := seed family p hf 16 member (113/50,3) (by decide +kernel)
  have b := seed family p hf 16 member (72/25,3) (by decide +kernel)
  norm_num at a b
  exact fun x low high => horizontal_segment _ _ _ _ _ a b (by norm_num) low high

theorem singleton_right (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (member : 32∈family) :
    ∀ y : ℝ,113/50≤y → y≤72/25 → (owner p 32).Inside 3 y := by
  have a := seed family p hf 32 member (3,113/50) (by decide +kernel)
  have b := seed family p hf 32 member (3,72/25) (by decide +kernel)
  norm_num at a b
  exact fun y low high => vertical_segment _ _ _ _ _ a b (by norm_num) low high

/-- Exact auxiliary labels supplied by the four actual singleton bars.
The combined indices are F0--F9 followed by G0--G9. -/
theorem singleton_pairs (family : Finset Nat) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (one : 1∈family) (two : 2∈family)
    (sixteen : 16∈family) (thirtytwo : 32∈family) :
    ({2,12} : Finset Nat)⊆auxiliaries p 1 ∧
      ({0,10} : Finset Nat)⊆auxiliaries p 2 ∧
      ({7,17} : Finset Nat)⊆auxiliaries p 16 ∧
      ({9,19} : Finset Nat)⊆auxiliaries p 32 := by
  have a := singleton_bottom family p hf one
  have b := singleton_left family p hf two
  have c := singleton_top family p hf sixteen
  have d := singleton_right family p hf thirtytwo
  refine ⟨?_,?_,?_,?_⟩
  all_goals intro j member; simp only [Finset.mem_insert,Finset.mem_singleton] at member
  · rcases member with rfl|rfl
    · apply (auxiliary_exact p 1 2 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact a _ (by norm_num) (by norm_num)
    · apply (auxiliary_exact p 1 12 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact a _ (by norm_num) le_rfl
  · rcases member with rfl|rfl
    · apply (auxiliary_exact p 2 0 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact b _ (by norm_num) le_rfl
    · apply (auxiliary_exact p 2 10 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact b _ (by norm_num) (by norm_num)
  · rcases member with rfl|rfl
    · apply (auxiliary_exact p 16 7 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact c _ (by norm_num) (by norm_num)
    · apply (auxiliary_exact p 16 17 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact c _ le_rfl (by norm_num)
  · rcases member with rfl|rfl
    · apply (auxiliary_exact p 32 9 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact d _ le_rfl (by norm_num)
    · apply (auxiliary_exact p 32 19 (by norm_num)).mp
      norm_num [auxPoints,fPoints,gPoints]
      exact d _ (by norm_num) (by norm_num)

end
#print axioms singleton_top
#print axioms singleton_right
end N12Compact.MergedPending
