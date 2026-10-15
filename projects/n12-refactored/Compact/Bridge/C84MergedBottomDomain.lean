import Compact.Bridge.OwnerBudget
import Compact.Geometry.C84MergedBottom
import S12.Diameter

/-! The genuine G-domain of the merged bottom/SE square in case84.
Its three possible singleton owners are derived from the actual packing,
not from the historical retained-row domain array. -/
namespace N12Compact.C84MergedBottomDomain
open S12 S12Pilot OwnerBudget
set_option Elab.async false

def allowed : List (Finset Nat) := [{5},{6},{8}]

/-- This geometric domain depends only on the original G-budget being two
exempt squares. No F-cardinality specialization is made. -/
noncomputable def domain (family : Finset Nat)
    (count : (family ∩ auxExempt 1).card=2) : HalfDomain family 8704 1 :=
  ⟨allowed, by
    intro p i hf hi
    have ha : 1<(p.square i).side := by rw [p.congruent]; exact p.side_gt_one
    have size : (p.square i).side≤1001/1000 := by
      rw [p.congruent]; exact p.side_le
    have markers : ExactMarkers (p.square i) (maskSupport 8704) := by
      simpa only [hi] using coded_exact p i
    have bottom : (p.square i).Inside 2 (457/500) := by
      have h := (markers 13).mpr (by decide +kernel)
      norm_num [Owns,marker] at h
      exact h
    have central : (p.square i).Inside (47/20) (33/20) := by
      have h := (markers 9).mpr (by decide +kernel)
      norm_num [Owns,marker] at h
      exact h
    have missing : ¬(p.square i).Inside (33/20) (33/20) := by
      intro h
      have h' : (p.square i).Inside (marker 8).1 (marker 8).2 := by
        norm_num [marker]
        exact h
      exact (by decide +kernel : (8 : Marker) ∉ maskSupport 8704)
        ((markers 8).mp h')
    have budget := nat_aux_budget p 1 i
    rw [hf,hi,count] at budget
    have nonexempt : 8704 ∉ auxExempt 1 := by decide +kernel
    simp only [nonexempt,if_false] at budget
    obtain ⟨j,singleton⟩ := Finset.card_eq_one.mp
      (show (natAuxOwners p 1 i).card=1 by omega)
    have member : j∈natAuxOwners p 1 i := by simp only [singleton,Finset.mem_singleton]
    have bound : j<10 := Finset.mem_range.mp (nat_aux_subset p 1 i member)
    have point := (nat_aux_exact p 1 i j
      (by simpa only [aux_kind_length] using List.mem_range.mpr bound)).mpr member
    have choice : j=5 ∨ j=6 ∨ j=8 := by
      by_cases five : j=5
      · exact Or.inl five
      have missingG5 : ¬(p.square i).Inside (113/50) 1 := by
        intro h
        have actual : (p.square i).Inside ((auxPoints (auxKind 1))[5]!).1
            ((auxPoints (auxKind 1))[5]!).2 := by
          norm_num [auxKind,auxPoints,gPoints]
          exact h
        have mem := (nat_aux_exact p 1 i 5 (by decide +kernel)).mp actual
        have equality : 5=j := by simpa only [singleton,Finset.mem_singleton] using mem
        exact five equality.symm
      have exclusions := C84MergedBottom.forbidden (p.square i) ha size
        bottom central missing missingG5
      interval_cases j
      · norm_num [auxKind,auxPoints,gPoints] at point
        exact False.elim (exclusions.1 point)
      · norm_num [auxKind,auxPoints,gPoints] at point
        have d := normalized_diameter_bound (p.square i) size _ _ _ _ bottom point
        norm_num at d
      · norm_num [auxKind,auxPoints,gPoints] at point
        exact False.elim (exclusions.2.1 point)
      · norm_num [auxKind,auxPoints,gPoints] at point
        exact False.elim (exclusions.2.2 point)
      · norm_num [auxKind,auxPoints,gPoints] at point
        have d := normalized_diameter_bound (p.square i) size _ _ _ _ bottom point
        norm_num at d
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · norm_num [auxKind,auxPoints,gPoints] at point
        have d := normalized_diameter_bound (p.square i) size _ _ _ _ bottom point
        norm_num at d
      · exact Or.inr (Or.inr rfl)
      · norm_num [auxKind,auxPoints,gPoints] at point
        have d := normalized_diameter_bound (p.square i) size _ _ _ _ bottom point
        norm_num at d
    rcases choice with rfl|rfl|rfl <;> simp only [singleton,allowed,List.mem_cons,
      List.mem_singleton,or_self,or_true,true_or]⟩

#print axioms domain
end N12Compact.C84MergedBottomDomain
