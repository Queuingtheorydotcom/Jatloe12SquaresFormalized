import Compact.Completion.CommonCases.C888C889Domains

/-! Shared genuine ownership entrance for original C888/C889.
Each finite cut ranges over a single ten-choice owner list. -/
namespace N12Compact.CommonCases.C888C889
open S12 S12Pilot OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

private def southChoices : List (Finset Nat) :=
  [{4,16},{4,18},{8,16},{8,18},{4,5,16},{4,8,16},{4,8,18},{4,9,16},{5,8,16},{8,9,16}]
private def northChoices : List (Finset Nat) :=
  [{5,16},{5,19},{9,16},{9,19},{4,5,16},{4,9,16},{5,8,16},{5,9,16},{5,9,19},{8,9,16}]
def Pattern (a n : Finset Nat) : Prop :=
  (({4,16} : Finset Nat)⊆a ∧ n∈([{5,19},{9,19},{5,9,19}] : List (Finset Nat))) ∨
  (({5,16} : Finset Nat)⊆n ∧ a∈([{4,18},{8,18},{4,8,18}] : List (Finset Nat)))

private theorem singleton_sets :
    (∀ s∈southwestAllowed,s=({2,12} : Finset Nat)) ∧
    (∀ s∈singletonAllowed,s=({7,17} : Finset Nat)) := by
  decide +kernel
private theorem bottom_filtered : ∀ a∈bottomAllowed,
    Disjoint a ({2,12} : Finset Nat) → a∈([{6,15},{4,6,15}] : List (Finset Nat)) := by
  decide +kernel
private theorem south_filtered : ∀ a∈southAllowed,
    Disjoint a ({6,15} : Finset Nat) → a∈southChoices := by decide +kernel
private theorem north_filtered : ∀ n∈northAllowed,
    Disjoint n ({7,17} : Finset Nat) → n∈northChoices := by decide +kernel
private theorem right_filtered : ∀ r∈rightAllowed,
    Disjoint r ({6,15} : Finset Nat) → Disjoint r ({7,17} : Finset Nat) →
    ({8,18} : Finset Nat)⊆r ∨ ({9,19} : Finset Nat)⊆r := by decide +kernel
private theorem lower_south : ∀ a∈southChoices,
    Disjoint a ({8,18} : Finset Nat) → ({4,16} : Finset Nat)⊆a := by decide +kernel
private theorem lower_north : ∀ n∈northChoices,
    16∉n → Disjoint n ({8,18} : Finset Nat) →
    n∈([{5,19},{9,19},{5,9,19}] : List (Finset Nat)) := by decide +kernel
private theorem upper_north : ∀ n∈northChoices,
    Disjoint n ({9,19} : Finset Nat) → ({5,16} : Finset Nat)⊆n := by decide +kernel
private theorem upper_south : ∀ a∈southChoices,
    16∉a → Disjoint a ({9,19} : Finset Nat) →
    a∈([{4,18},{8,18},{4,8,18}] : List (Finset Nat)) := by decide +kernel

theorem seed_point (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family b) (mask : Nat) (hm : mask∈family b) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed (family b) p hf mask hm P checked
theorem auxiliary_point (p : NormalizedPacking) (mask : Nat) (owned : Finset Nat)
    (sub : owned⊆auxiliaries p mask) (j : Nat) (bound : j<20) (member : j∈owned) :
    (owner p mask).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 :=
  (auxiliary_exact p mask j bound).mpr (sub member)
theorem missing_auxiliary (p : NormalizedPacking) (mask : Nat) (owned : Finset Nat)
    (equal : auxiliaries p mask=owned) (j : Nat) (bound : j<20) (missing : j∉owned) :
    ¬(owner p mask).Inside ((auxPoints 2)[j]!).1 ((auxPoints 2)[j]!).2 := by
  intro own
  have member := (auxiliary_exact p mask j bound).mp own
  rw [equal] at member
  exact missing member

theorem entrance (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family b) :
    ({6,15} : Finset Nat)⊆auxiliaries p 8192 ∧
      Pattern (auxiliaries p 512) (auxiliaries p 1024) := by
  have sw := singleton_sets.1 _
    (domain (family b) (southwestDomain b) p hf (by cases b <;> decide +kernel))
  have tr := singleton_sets.2 _
    (domain (family b) (singletonDomain b) p hf (by cases b <;> decide +kernel))
  change auxiliaries p 1=({2,12} : Finset Nat) at sw
  change auxiliaries p 16=({7,17} : Finset Nat) at tr
  have bottomSW := auxiliary_disjoint (family b) p hf 8192 1
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) (by decide +kernel)
  rw [sw] at bottomSW
  have bottomOptions := bottom_filtered _
    (domain (family b) (bottomDomain b) p hf (by cases b <;> decide +kernel)) bottomSW
  have bottom : ({6,15} : Finset Nat)⊆auxiliaries p 8192 := by
    have checked : ∀ a∈([{6,15},{4,6,15}] : List (Finset Nat)),({6,15} : Finset Nat)⊆a := by
      decide +kernel
    exact checked _ bottomOptions
  have southBottom := auxiliary_disjoint (family b) p hf 512 8192
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) (by decide +kernel)
  have northSingleton := auxiliary_disjoint (family b) p hf 1024 16
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) (by decide +kernel)
  rw [tr] at northSingleton
  have south := south_filtered _
    (domain (family b) (southDomain b) p hf (by cases b <;> decide +kernel))
    (southBottom.mono_right bottom)
  have north := north_filtered _
    (domain (family b) (northDomain b) p hf (by cases b <;> decide +kernel)) northSingleton
  have rightPair : ({8,18} : Finset Nat)⊆auxiliaries p (rightMask b) ∨
      ({9,19} : Finset Nat)⊆auxiliaries p (rightMask b) := by
    cases b
    · have rightBottom := auxiliary_disjoint (family false) p hf 16384 8192
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
      have rightSingleton := auxiliary_disjoint (family false) p hf 16384 16
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
      rw [tr] at rightSingleton
      exact right_filtered _ (domain (family false) rightDomain p hf (by decide +kernel))
        (rightBottom.mono_right bottom) rightSingleton
    · right
      have lo : (owner p 16416).Inside 3 (9/4) := by
        have h := seed_point true p hf 16416 (by decide +kernel) (3,9/4) (by decide +kernel)
        norm_num at h; exact h
      have hi : (owner p 16416).Inside 3 (11/4) := by
        have h := seed_point true p hf 16416 (by decide +kernel) (3,11/4) (by decide +kernel)
        norm_num at h; exact h
      have f : (owner p 16416).Inside 3 (113/50) := by
        have h := inside_segment (owner p 16416) 3 (9/4) 3 (11/4) (1/50) lo hi
          (by norm_num) (by norm_num)
        norm_num at h; exact h
      have g : (owner p 16416).Inside 3 (12/5) := by
        have h := inside_segment (owner p 16416) 3 (9/4) 3 (11/4) (3/10) lo hi
          (by norm_num) (by norm_num)
        norm_num at h; exact h
      have fMember : 9∈auxiliaries p 16416 := by
        apply (auxiliary_exact p 16416 9 (by norm_num)).mp
        norm_num [auxPoints,fPoints,gPoints]; exact f
      have gMember : 19∈auxiliaries p 16416 := by
        apply (auxiliary_exact p 16416 19 (by norm_num)).mp
        norm_num [auxPoints,fPoints,gPoints]; exact g
      intro j hj
      simp only [Finset.mem_insert,Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · exact fMember
      · exact gMember
  have aRight := auxiliary_disjoint (family b) p hf 512 (rightMask b)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)
  have nRight := auxiliary_disjoint (family b) p hf 1024 (rightMask b)
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
    (by cases b <;> decide +kernel)
  have central := auxiliary_disjoint (family b) p hf 512 1024
    (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) (by decide +kernel)
  refine ⟨bottom,?_⟩
  rcases rightPair with lower | upper
  · have aPair := lower_south _ south (aRight.mono_right lower)
    have missing : 16∉auxiliaries p 1024 := fun own =>
      Finset.disjoint_left.mp central (aPair (by decide +kernel)) own
    exact Or.inl ⟨aPair,lower_north _ north missing (nRight.mono_right lower)⟩
  · have nPair := upper_north _ north (nRight.mono_right upper)
    have missing : 16∉auxiliaries p 512 := fun own =>
      Finset.disjoint_left.mp central own (nPair (by decide +kernel))
    exact Or.inr ⟨nPair,upper_south _ south missing (aRight.mono_right upper)⟩


#print axioms entrance
end
end N12Compact.CommonCases.C888C889
