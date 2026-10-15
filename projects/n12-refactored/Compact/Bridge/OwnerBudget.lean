import S12.CertifiedDomain

/-! Finite owner domains coming directly from the original packing budget.
Missing local refinements are safely replaced by all ten singleton choices;
their global consistency can then be checked by `certified_domain_forced`.
-/
namespace N12Compact.OwnerBudget
open S12

def singletonChoices : List (Finset Nat) := (List.range 10).map (fun i => {i})

theorem singleton_choices_complete (s : Finset Nat) (hsub : s ⊆ Finset.range 10)
    (hcard : s.card = 1) : s ∈ singletonChoices := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr
    (Finset.mem_range.mp (hsub (Finset.mem_singleton_self i))), rfl⟩

structure HalfDomain (family : Finset Nat) (mask : Nat) (k : Fin 2) where
  allowed : List (Finset Nat)
  sound : ∀ (p : NormalizedPacking) (i : Fin 12), codedMarkerFamily p = family →
    markerCode p i = mask → natAuxOwners p k i ∈ allowed

def HalfDomain.ofSpec (family : Finset Nat) (w : SingleSpec) (k : Fin 2)
    (hw : w.Check) (hm : w.Matches family k) : HalfDomain family w.mask k :=
  ⟨w.allowed, w.actual hw family k hm⟩

def HalfDomain.singleton (family : Finset Nat) (mask : Nat) (k : Fin 2)
    (hcount : (family ∩ auxExempt k).card = 2) (hm : mask ∉ auxExempt k) :
    HalfDomain family mask k :=
  ⟨singletonChoices, by
    intro p i hf hi
    have hb := nat_aux_budget p k i
    rw [hf, hi, hcount] at hb
    simp only [hm, if_false] at hb
    exact singleton_choices_complete _ (nat_aux_subset p k i) (by omega)⟩

def HalfDomain.empty (family : Finset Nat) (mask : Nat) (k : Fin 2)
    (hcount : (family ∩ auxExempt k).card = 2) (hm : mask ∈ auxExempt k) :
    HalfDomain family mask k :=
  ⟨[∅], by
    intro p i hf hi
    have hb := nat_aux_budget p k i
    rw [hf, hi, hcount] at hb
    simp only [hm, if_true] at hb
    have he : natAuxOwners p k i = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [he, List.mem_singleton]⟩

/-- A wall or singleton seed can itself determine an auxiliary owner. The
triangle certificate is checked rational convexity, not an angle enclosure. -/
def HalfDomain.ofSeedHull (family : Finset Nat) (mask : Nat) (k : Fin 2)
    (index : Nat) (hindex : index ∈ List.range (auxPoints (auxKind k)).length)
    (hcount : (family ∩ auxExempt k).card = 2) (hm : mask ∉ auxExempt k)
    (w : TriangleCertificate) (hw : w.Check)
    (htarget : w.target = (auxPoints (auxKind k))[index]!)
    (h0 : w.p0 ∈ seedPoints (maskSupport mask))
    (h1 : w.p1 ∈ seedPoints (maskSupport mask))
    (h2 : w.p2 ∈ seedPoints (maskSupport mask)) : HalfDomain family mask k :=
  ⟨[{index}], by
    intro p i hf hi
    have hb := nat_aux_budget p k i
    rw [hf, hi, hcount] at hb
    simp only [hm, if_false] at hb
    have hs := seed_points_sound (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (maskSupport mask) (by simpa only [hi] using coded_exact p i)
    have hp := triangle_certificate_sound w hw (p.square i)
      (hs _ h0) (hs _ h1) (hs _ h2)
    rw [htarget] at hp
    have hn := (nat_aux_exact p k i index hindex).mp hp
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (show (natAuxOwners p k i).card = 1 by omega)
    have he : index = j := by simpa only [hj, Finset.mem_singleton] using hn
    simpa only [List.mem_singleton, he] using hj⟩

def product (family : Finset Nat) (mask : Nat)
    (a : HalfDomain family mask 0) (b : HalfDomain family mask 1) :
    CertifiedDomain family :=
  ⟨mask, a.allowed.flatMap (fun x => b.allowed.map (combinedOwners x)), by
    intro p i hf hi
    exact List.mem_flatMap.mpr ⟨_, a.sound p i hf hi,
      List.mem_map.mpr ⟨_, b.sound p i hf hi, rfl⟩⟩⟩

#print axioms product
end N12Compact.OwnerBudget
