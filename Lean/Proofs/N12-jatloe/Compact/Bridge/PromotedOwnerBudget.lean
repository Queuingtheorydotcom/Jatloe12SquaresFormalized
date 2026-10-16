import Compact.Bridge.OwnerBudget

/-! An exempt owner can be promoted when a strict seed hull forces it to own
an auxiliary point. Removing that owner from the exemption set restores the
ordinary ten-point budget, without assuming the saved refined domains. -/
namespace N12Compact.OwnerBudget
open S12 S12Pilot

structure Promotion (family : Finset Nat) where
  mask : Nat
  member : mask ∈ family
  exempt : ∀ k, mask ∈ auxExempt k
  count : ∀ k, (family ∩ auxExempt k).card = 3
  index : Fin 2 → Fin 10
  witness : Fin 2 → TriangleCertificate
  checked : ∀ k, (witness k).Check ∧
    (witness k).target = (auxPoints (auxKind k))[(index k).val]! ∧
    (witness k).p0 ∈ seedPoints (maskSupport mask) ∧
    (witness k).p1 ∈ seedPoints (maskSupport mask) ∧
    (witness k).p2 ∈ seedPoints (maskSupport mask)

theorem Promotion.owns {family : Finset Nat} (d : Promotion family)
    (p : NormalizedPacking) (k : Fin 2) (i : Fin 12)
    (hi : markerCode p i = d.mask) : (d.index k).val ∈ natAuxOwners p k i := by
  obtain ⟨hw, ht, h0, h1, h2⟩ := d.checked k
  have hs := seed_points_sound (p.square i)
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained i)
    _ (by simpa only [hi] using coded_exact p i)
  have hp := triangle_certificate_sound (d.witness k) hw (p.square i)
    (hs _ h0) (hs _ h1) (hs _ h2)
  rw [ht] at hp
  exact (nat_aux_exact p k i (d.index k).val
    (by simpa only [aux_kind_length] using List.mem_range.mpr (d.index k).isLt)).mp hp

theorem Promotion.card_le_one {family : Finset Nat} (d : Promotion family)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (i : Fin 12) : (natAuxOwners p k i).card ≤ 1 := by
  classical
  let j := ownerIndex p d.mask
  have hj : markerCode p j = d.mask := ownerIndex_spec p d.mask (by rw [hf]; exact d.member)
  have jmem : j ∈ auxExemptIndices p k := by
    simp only [auxExemptIndices, Finset.mem_filter, Finset.mem_univ, true_and, hj]
    exact d.exempt k
  have ec : (auxExemptIndices p k).card = 3 := by
    rw [← Finset.card_image_of_injective _ (markerCode_injective p), aux_exempt_image, hf]
    exact d.count k
  have ec' : ((auxExemptIndices p k).erase j).card = 2 := by
    rw [Finset.card_erase_of_mem jmem, ec]
  have force : ∀ r, r ∉ (auxExemptIndices p k).erase j →
      (sortedAuxOwners p k r).Nonempty := by
    intro r hr
    by_cases he : r = j
    · subst r
      have hn := d.owns p k j hj
      have hc : 0 < (natAuxOwners p k j).card := Finset.card_pos.mpr ⟨_, hn⟩
      rw [nat_aux_card] at hc
      exact Finset.card_pos.mp hc
    · exact sorted_aux_forced p k r (fun h => hr (Finset.mem_erase.mpr ⟨he,h⟩))
  have hb := individual_budget (sortedAuxOwners p k)
    ((auxExemptIndices p k).erase j) (sorted_aux_disjoint p k) force i
  rw [← nat_aux_card, ec'] at hb
  split_ifs at hb <;> omega

theorem Promotion.card_one {family : Finset Nat} (d : Promotion family)
    (mask : Nat) (k : Fin 2) (hn : mask ∉ auxExempt k ∨ mask = d.mask)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 12) (hi : markerCode p i = mask) : (natAuxOwners p k i).card = 1 := by
  have hu := d.card_le_one p hf k i
  have hl : 1 ≤ (natAuxOwners p k i).card := by
    rcases hn with hn | rfl
    · have hb := (nat_aux_budget p k i).1
      simpa only [hi, hn, if_false] using hb
    · exact Finset.card_pos.mpr ⟨_, d.owns p k i hi⟩
  omega

def Promotion.ofSpec {family : Finset Nat} (d : Promotion family)
    (w : SingleSpec) (k : Fin 2) (hw : w.Check)
    (hk : w.kind = auxKind k) (hl : w.lower = 1) (hu : w.upper = 1)
    (hn : w.mask ∉ auxExempt k) : HalfDomain family w.mask k :=
  ⟨w.allowed, by
    intro p i hf hi
    have hc := d.card_one w.mask k (Or.inl hn) p hf i hi
    exact w.sound hw (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (by simpa only [hi] using coded_exact p i) (natAuxOwners p k i)
      (by simpa only [hk] using nat_aux_exact p k i) (nat_aux_subset p k i)
      (by omega) (by omega)⟩

def Promotion.singleton {family : Finset Nat} (d : Promotion family)
    (mask : Nat) (k : Fin 2) (hn : mask ∉ auxExempt k) : HalfDomain family mask k :=
  ⟨singletonChoices, by
    intro p i hf hi
    exact singleton_choices_complete _ (nat_aux_subset p k i)
      (d.card_one mask k (Or.inl hn) p hf i hi)⟩

def Promotion.ownDomain {family : Finset Nat} (d : Promotion family)
    (k : Fin 2) : HalfDomain family d.mask k :=
  ⟨[{(d.index k).val}], by
    intro p i hf hi
    obtain ⟨n, hn⟩ := Finset.card_eq_one.mp
      (d.card_one d.mask k (Or.inr rfl) p hf i hi)
    have he : (d.index k).val = n := by
      simpa only [hn, Finset.mem_singleton] using d.owns p k i hi
    simpa only [List.mem_singleton, he] using hn⟩

def Promotion.combined {family : Finset Nat} (d : Promotion family)
    (w : CombinedSpec) (hw : w.Check)
    (hl0 : w.first.val.lower = 1) (hu0 : w.first.val.upper = 1)
    (hl1 : w.second.val.lower = 1) (hu1 : w.second.val.upper = 1)
    (hn0 : w.first.val.mask ∉ auxExempt 0)
    (hn1 : w.second.val.mask ∉ auxExempt 1) : CertifiedDomain family :=
  ⟨w.mask, w.allowed, by
    intro p i hf hi
    let first := d.ofSpec w.first.val 0 w.first.property
      hw.2.2.1 hl0 hu0 hn0
    let second := d.ofSpec w.second.val 1 w.second.property
      hw.2.2.2.1 hl1 hu1 hn1
    exact w.sound hw (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (by simpa only [hi] using coded_exact p i)
      (natAuxOwners p 0 i) (natAuxOwners p 1 i)
      (first.sound p i hf (hi.trans hw.1.symm))
      (second.sound p i hf (hi.trans hw.2.1.symm))
      (nat_combined_exact p i)⟩

#print axioms Promotion.card_le_one
end N12Compact.OwnerBudget
