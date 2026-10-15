import Compact.Completion.OtherCases.MergedPending.Families
import S12.DomainSpecData

/-! Authentic small ownership deductions for the pending merged cases.
The existing checked local specifications are used at their original
1..2 budgets. Each family-specific bound is proved from its actual F/G
census; no historical vector list is accepted as a premise.
Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners RelaxedOwnerDomain
set_option Elab.async false
noncomputable section

private def southDomain (k : Case) : CertifiedDomain (family k) :=
  ofCombined _ combinedSpec6 combinedSpec6_checked
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
private def leftDomain (k : Case) : CertifiedDomain (family k) :=
  ofCombined _ combinedSpec17 combinedSpec17_checked
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
private def bottomDomain (k : Case) : CertifiedDomain (family k) :=
  ofCombined _ combinedSpec19 combinedSpec19_checked
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
private def topDomain (k : Case) : CertifiedDomain (family k) :=
  ofCombined _ combinedSpec24 combinedSpec24_checked
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
private def rightDomain (k : Case) : CertifiedDomain (family k) :=
  ofCombined _ combinedSpec21 combinedSpec21_checked
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
private def southeastDomain (k : Case) : CertifiedDomain (family k) :=
  ofCombined _ combinedSpec8 combinedSpec8_checked
    (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)

private theorem south_cut : ∀ a∈combinedSpec6.allowed,
    0∉a → 2∉a → 10∉a → 12∉a → 4∈a ∧ 13∈a := by decide +kernel
private theorem left_cut : ∀ a∈combinedSpec17.allowed,
    0∉a → 1∈a ∧ 11∈a := by decide +kernel
private theorem bottom_cut : ∀ a∈combinedSpec19.allowed,
    2∉a → 6∈a ∧ 15∈a := by decide +kernel
private theorem top_cut : ∀ a∈combinedSpec24.allowed,
    7∉a → 3∈a ∧ 14∈a := by decide +kernel
private theorem right_cut : ∀ a∈combinedSpec21.allowed,
    9∉a → 8∈a ∧ 18∈a := by decide +kernel
private theorem southeast_cut : ∀ a∈combinedSpec8.allowed,
    4∉a → 6∉a → 8∈a := by decide +kernel
private theorem right_upper_cut : ∀ a∈combinedSpec21.allowed,
    8∉a → 9∈a ∧ 19∈a := by decide +kernel

theorem foreign_auxiliary (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (m n j : Nat)
    (hm : m∈family k) (hn : n∈family k) (different : m≠n)
    (owned : j∈auxiliaries p n) : j∉auxiliaries p m :=
  fun own => Finset.disjoint_left.mp (auxiliary_disjoint _ p hf m n hm hn different) own owned

structure CommonLabels (p : NormalizedPacking) : Prop where
  south : 4∈auxiliaries p 256 ∧ 13∈auxiliaries p 256
  left : 1∈auxiliaries p 4096 ∧ 11∈auxiliaries p 4096
  bottom : 6∈auxiliaries p 8192 ∧ 15∈auxiliaries p 8192
  top : 3∈auxiliaries p 32768 ∧ 14∈auxiliaries p 32768

theorem common_labels (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) : CommonLabels p := by
  have w := walls k p hf
  have swF : 2∈auxiliaries p 1 := by
    apply (auxiliary_exact p 1 2 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact w.bottomSingleton _ (by norm_num) (by norm_num)
  have swG : 12∈auxiliaries p 1 := by
    apply (auxiliary_exact p 1 12 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact w.bottomSingleton _ (by norm_num) le_rfl
  have leftF : 0∈auxiliaries p 2 := by
    apply (auxiliary_exact p 2 0 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact w.leftSingleton _ (by norm_num) le_rfl
  have leftG : 10∈auxiliaries p 2 := by
    apply (auxiliary_exact p 2 10 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact w.leftSingleton _ (by norm_num) (by norm_num)
  have topF : 7∈auxiliaries p 16 := by
    apply (auxiliary_exact p 16 7 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact w.topSingleton _ (by norm_num) (by norm_num)
  have foreign (m n j : Nat)
      (hm : m∈({1,2,12,16,192,256,4096,8192,32768} : Finset Nat))
      (hn : n∈({1,2,12,16,192,256,4096,8192,32768} : Finset Nat))
      (different : m≠n) (owned : j∈auxiliaries p n) : j∉auxiliaries p m :=
    foreign_auxiliary k p hf m n j (common_member k m hm) (common_member k n hn) different owned
  refine ⟨?_,?_,?_,?_⟩
  · exact south_cut _ (domain _ (southDomain k) p hf (common_member k 256 (by decide)))
      (foreign 256 2 0 (by decide) (by decide) (by decide) leftF)
      (foreign 256 1 2 (by decide) (by decide) (by decide) swF)
      (foreign 256 2 10 (by decide) (by decide) (by decide) leftG)
      (foreign 256 1 12 (by decide) (by decide) (by decide) swG)
  · exact left_cut _ (domain _ (leftDomain k) p hf (common_member k 4096 (by decide)))
      (foreign 4096 2 0 (by decide) (by decide) (by decide) leftF)
  · exact bottom_cut _ (domain _ (bottomDomain k) p hf (common_member k 8192 (by decide)))
      (foreign 8192 1 2 (by decide) (by decide) (by decide) swF)
  · exact top_cut _ (domain _ (topDomain k) p hf (common_member k 32768 (by decide)))
      (foreign 32768 16 7 (by decide) (by decide) (by decide) topF)

theorem c700_right_labels (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    8∈auxiliaries p 16384 ∧ 18∈auxiliaries p 16384 := by
  have nine : 9∈auxiliaries p 32 := by
    apply (auxiliary_exact p 32 9 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact c700_right_singleton p hf _ le_rfl (by norm_num)
  exact right_cut _ (domain _ (rightDomain .c700) p hf (by decide +kernel))
    (foreign_auxiliary .c700 p hf 16384 32 9 (by decide +kernel) (by decide +kernel) (by decide) nine)

/-- In the upper-merged cases F8 belongs to actual southeast512. It
therefore cannot be borrowed as a lower right-wall point. -/
theorem southeast_lower (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k) :
    8∈auxiliaries p 512 := by
  have labels := common_labels k p hf
  exact southeast_cut _ (domain _ (southeastDomain k) p hf member)
    (foreign_auxiliary k p hf 512 256 4 member (common_member k 256 (by decide))
      (by decide) labels.south.1)
    (foreign_auxiliary k p hf 512 8192 6 member (common_member k 8192 (by decide))
      (by decide) labels.bottom.1)

/-- C867's actual right wall points upward, unlike C700's right wall.
Both actual foreign-owner deductions are supplied before the domain cut. -/
theorem c867_right_labels (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c867) :
    9∈auxiliaries p 16384 ∧ 19∈auxiliaries p 16384 := by
  have eight := southeast_lower .c867 p hf (by decide +kernel)
  exact right_upper_cut _ (domain _ (rightDomain .c867) p hf (by decide +kernel))
    (foreign_auxiliary .c867 p hf 16384 512 8 (by decide +kernel) (by decide +kernel) (by decide) eight)

end
#print axioms common_labels
#print axioms southeast_lower
#print axioms c867_right_labels
end N12Compact.MergedPending
