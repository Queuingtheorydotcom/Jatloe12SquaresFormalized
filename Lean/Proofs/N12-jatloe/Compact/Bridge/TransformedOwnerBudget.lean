import Compact.Bridge.OwnerBudget

/-! Reuse a proved one-point auxiliary domain under a container symmetry.
This transports the actual square, its complete marker ownership, and every
auxiliary point; it does not transfer a sampled orientation certificate. -/
namespace N12Compact.OwnerBudget
open S12 S12Pilot

noncomputable def HalfDomain.ofTransformedSingletonSpec
    (family : Finset Nat) (mask : Nat) (k sourceKind : Fin 2)
    (t : Transform) (ht : t ∈ allTransforms)
    (w : SingleSpec) (hw : w.Check)
    (hkind : w.kind = auxKind sourceKind) (hlo : w.lower = 1) (hhi : w.upper = 1)
    (hm : w.mask ∈ candidateMasks) (hmask : t.maskAction w.mask = mask)
    (perm : Fin 10 ≃ Fin 10)
    (hp : ∀ j : Fin 10, t.applyRat ((auxPoints (auxKind sourceKind))[j.val]!) =
      (auxPoints (auxKind k))[(perm j).val]!)
    (allowed : List (Finset Nat))
    (hallowed : ∀ j : Fin 10, {j.val} ∈ w.allowed → {(perm j).val} ∈ allowed)
    (hcount : (family ∩ auxExempt k).card = 2) (hne : mask ∉ auxExempt k) :
    HalfDomain family mask k :=
  ⟨allowed, by
    intro p i hf hi
    have hb := nat_aux_budget p k i
    rw [hf, hi, hcount] at hb
    simp only [hne, if_false] at hb
    obtain ⟨n, hn⟩ := Finset.card_eq_one.mp (show (natAuxOwners p k i).card = 1 by omega)
    have nlt : n < 10 := Finset.mem_range.mp (nat_aux_subset p k i
      (by rw [hn]; exact Finset.mem_singleton_self _))
    let N : Fin 10 := ⟨n,nlt⟩
    let J := perm.symm N
    have transformed : AuxExact (t.pull (p.square i)) (auxKind sourceKind) {J.val} := by
      intro j hj
      have jlt : j < 10 := by simpa only [aux_kind_length] using List.mem_range.mp hj
      let I : Fin 10 := ⟨j,jlt⟩
      rw [rat_inside_transform]
      have hpoint := hp I
      change t.applyRat ((auxPoints (auxKind sourceKind))[j]!) =
        (auxPoints (auxKind k))[(perm I).val]! at hpoint
      rw [hpoint]
      rw [nat_aux_exact p k i (perm I).val
        (by simpa only [aux_kind_length] using List.mem_range.mpr (perm I).isLt)]
      rw [hn, Finset.mem_singleton, Finset.mem_singleton]
      change (perm I).val = N.val ↔ I.val = J.val
      constructor
      · intro he
        have he' : perm I = N := Fin.ext he
        have hJ : perm J = N := perm.apply_symm_apply N
        exact congrArg Fin.val (perm.injective (he'.trans hJ.symm))
      · intro he
        have he' : I = J := Fin.ext he
        rw [he']
        exact congrArg Fin.val (perm.apply_symm_apply N)
    have hmarkers := exact_markers_pull t ht (p.square i) w.mask hm
      (by simpa only [hmask, hi] using coded_exact p i)
    have hlocal := w.sound hw (t.pull (p.square i))
      (by simpa only [pull_same_side, p.congruent] using p.side_gt_one)
      (by simpa only [pull_same_side, p.congruent] using p.side_le)
      (container_transform t _ (p.contained i)) hmarkers {J.val}
      (by simpa only [hkind] using transformed)
      (by
        intro j hj
        rw [Finset.mem_singleton.mp hj]
        exact Finset.mem_range.mpr J.isLt)
      (by simp only [hlo, Finset.card_singleton]; exact le_rfl)
      (by simp only [hhi, Finset.card_singleton]; exact le_rfl)
    have result := hallowed J hlocal
    simpa only [J, perm.apply_symm_apply, N, hn] using result⟩

noncomputable def reflectXF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![8,9,6,7,4,5,2,3,0,1] (by decide +kernel)

noncomputable def turnFG : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![4,7,1,9,3,6,0,8,2,5] (by decide +kernel)

#print axioms HalfDomain.ofTransformedSingletonSpec
end N12Compact.OwnerBudget
