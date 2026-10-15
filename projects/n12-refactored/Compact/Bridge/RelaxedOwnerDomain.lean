import Compact.Bridge.OwnerBudget
import Compact.Bridge.SmallOwnerDomain

/-! Reuse checked ownership specifications with a larger cardinality interval
than the actual packing needs. Transported specifications act on the whole
owned set, retaining the original marker and auxiliary point geometry. -/

set_option Elab.async false

namespace N12Compact.RelaxedOwnerDomain
open S12 S12Pilot
noncomputable section

def lower (mask : Nat) (k : Fin 2) : Nat :=
  if mask ∈ auxExempt k then 0 else 1

def upper (family : Finset Nat) (mask : Nat) (k : Fin 2) : Nat :=
  (family ∩ auxExempt k).card - 2 + lower mask k

/-- The checked specification may cover more cardinalities than are possible
in this actual family. Its lower/upper endpoints need not equal the budget. -/
def Bounds (family : Finset Nat) (mask : Nat) (w : SingleSpec) (k : Fin 2) : Prop :=
  w.lower ≤ lower mask k ∧ upper family mask k ≤ w.upper

instance (family : Finset Nat) (mask : Nat) (w : SingleSpec) (k : Fin 2) :
    Decidable (Bounds family mask w k) := inferInstanceAs (Decidable (_ ∧ _))

theorem actual_bounds (family : Finset Nat) (mask : Nat) (w : SingleSpec) (k : Fin 2)
    (bounds : Bounds family mask w k) (p : NormalizedPacking) (i : Fin 12)
    (hf : codedMarkerFamily p = family) (hi : markerCode p i = mask) :
    w.lower ≤ (natAuxOwners p k i).card ∧
      (natAuxOwners p k i).card ≤ w.upper := by
  have h := nat_aux_budget p k i
  rw [hf, hi] at h
  exact ⟨bounds.1.trans h.1, h.2.trans bounds.2⟩

def firstHalf (owned : Finset Nat) : Finset Nat := owned.filter (fun n => n < 10)
def secondHalf (owned : Finset Nat) : Finset Nat := owned.filter (fun n => 10 ≤ n)

theorem firstHalf_combined (x y : Finset Nat) (hx : x ⊆ Finset.range 10) :
    firstHalf (combinedOwners x y) = x := by
  ext n
  simp only [firstHalf, Finset.mem_filter]
  constructor
  · rintro ⟨h,hn⟩
    exact (mem_combined_low x y n hn).mp h
  · intro h
    have hn := Finset.mem_range.mp (hx h)
    exact ⟨(mem_combined_low x y n hn).mpr h,hn⟩

theorem secondHalf_combined (x y : Finset Nat) (hx : x ⊆ Finset.range 10) :
    secondHalf (combinedOwners x y) = y.image (fun n => n+10) := by
  ext n
  simp only [secondHalf, Finset.mem_filter]
  constructor
  · rintro ⟨h,hn⟩
    exact Finset.mem_image.mpr
      ⟨n-10,(mem_combined_high x y hx n hn).mp h,by omega⟩
  · intro h
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
    refine ⟨?_,by omega⟩
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨j,hj,rfl⟩))

def SetBounds (family : Finset Nat) (mask : Nat) (owned : Finset Nat) : Prop :=
  (lower mask 0 ≤ (firstHalf owned).card ∧
    (firstHalf owned).card ≤ upper family mask 0) ∧
  (lower mask 1 ≤ (secondHalf owned).card ∧
    (secondHalf owned).card ≤ upper family mask 1)

instance (family : Finset Nat) (mask : Nat) (owned : Finset Nat) :
    Decidable (SetBounds family mask owned) := inferInstanceAs (Decidable ((_ ∧ _) ∧ (_ ∧ _)))

/-- Remove the extra cardinalities admitted by a deliberately weaker spec.
The output still describes the complete actual twenty-point ownership set. -/
def restrictByBudget (family : Finset Nat) (d : CertifiedDomain family) :
    CertifiedDomain family :=
  ⟨d.mask, d.allowed.filter (fun owned => decide (SetBounds family d.mask owned)), by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨d.sound p i hf hi,decide_eq_true ?_⟩
    have hF := nat_aux_budget p 0 i
    have hG := nat_aux_budget p 1 i
    rw [hf,hi] at hF hG
    unfold SetBounds natCombinedOwners
    rw [firstHalf_combined _ _ (nat_aux_subset p 0 i),
      secondHalf_combined _ _ (nat_aux_subset p 0 i),
      Finset.card_image_of_injective _ (show Function.Injective (fun n : Nat => n+10) by
        intro a b h
        change a+10=b+10 at h
        exact Nat.add_right_cancel h)]
    exact ⟨hF,hG⟩⟩

/-- The common F-count-two specialization, keeping a small transparent filter
for the concrete nine-owner domain enumeration. -/
def restrictFCardOne (family : Finset Nat) (d : CertifiedDomain family)
    (hcount : (family ∩ auxExempt 0).card = 2)
    (hne : d.mask ∉ auxExempt 0) : CertifiedDomain family :=
  ⟨d.mask, d.allowed.filter (fun owned =>
      decide ((owned.filter (fun n => n < 10)).card = 1)), by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨d.sound p i hf hi,decide_eq_true ?_⟩
    have hb := nat_aux_budget p 0 i
    rw [hf,hi,hcount] at hb
    simp only [hne,if_false] at hb
    change (firstHalf (combinedOwners (natAuxOwners p 0 i) (natAuxOwners p 1 i))).card = 1
    rw [firstHalf_combined _ _ (nat_aux_subset p 0 i)]
    omega⟩

/-- A broad half-domain can be generated from the actual budget alone.
Only the 56 subsets of size at most two are listed. -/
def ofSmallBudget (family : Finset Nat) (mask : Nat) (k : Fin 2)
    (small : upper family mask k ≤ 2) : OwnerBudget.HalfDomain family mask k :=
  ⟨SmallOwnerDomain.smallSubsets.filter (fun owned =>
      decide (lower mask k ≤ owned.card ∧ owned.card ≤ upper family mask k)), by
    intro p i hf hi
    have hb := nat_aux_budget p k i
    rw [hf,hi] at hb
    exact List.mem_filter.mpr
      ⟨SmallOwnerDomain.smallSubsets_complete _ (nat_aux_subset p k i)
        (hb.2.trans small),decide_eq_true hb⟩⟩

/-- The same broad domain with a genuine forced seed-hull point retained. -/
def ofSmallBudgetWithSeed (family : Finset Nat) (mask : Nat) (k : Fin 2)
    (small : upper family mask k ≤ 2)
    (index : Nat) (hindex : index ∈ List.range (auxPoints (auxKind k)).length)
    (w : TriangleCertificate) (hw : w.Check)
    (htarget : w.target = (auxPoints (auxKind k))[index]!)
    (h0 : w.p0 ∈ seedPoints (maskSupport mask))
    (h1 : w.p1 ∈ seedPoints (maskSupport mask))
    (h2 : w.p2 ∈ seedPoints (maskSupport mask)) : OwnerBudget.HalfDomain family mask k :=
  ⟨(ofSmallBudget family mask k small).allowed.filter (fun owned => decide (index ∈ owned)), by
    intro p i hf hi
    apply List.mem_filter.mpr
    refine ⟨(ofSmallBudget family mask k small).sound p i hf hi,decide_eq_true ?_⟩
    have seeds := seed_points_sound (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (maskSupport mask) (by simpa only [hi] using coded_exact p i)
    have point := triangle_certificate_sound w hw (p.square i)
      (seeds _ h0) (seeds _ h1) (seeds _ h2)
    rw [htarget] at point
    exact (nat_aux_exact p k i index hindex).mp point⟩

theorem single_actual (family : Finset Nat) (w : SingleSpec) (hw : w.Check)
    (k : Fin 2) (hk : w.kind = auxKind k)
    (bounds : Bounds family w.mask w k)
    (p : NormalizedPacking) (i : Fin 12)
    (hf : codedMarkerFamily p = family) (hi : markerCode p i = w.mask) :
    natAuxOwners p k i ∈ w.allowed := by
  have hb := actual_bounds family w.mask w k bounds p i hf hi
  exact w.sound hw (p.square i)
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained i)
    (by simpa only [hi] using coded_exact p i) _
    (by simpa only [hk] using nat_aux_exact p k i)
    (nat_aux_subset p k i) hb.1 hb.2

def ofSingle (family : Finset Nat) (w : SingleSpec) (hw : w.Check)
    (k : Fin 2) (hk : w.kind = auxKind k)
    (bounds : Bounds family w.mask w k) : OwnerBudget.HalfDomain family w.mask k :=
  ⟨w.allowed, single_actual family w hw k hk bounds⟩

def ofCombined (family : Finset Nat) (w : CombinedSpec) (hw : w.Check)
    (hF : Bounds family w.mask w.first.val 0)
    (hG : Bounds family w.mask w.second.val 1) : CertifiedDomain family :=
  ⟨w.mask, w.allowed, by
    intro p i hf hi
    have hF' : Bounds family w.first.val.mask w.first.val 0 := by
      simpa only [hw.1] using hF
    have hG' : Bounds family w.second.val.mask w.second.val 1 := by
      simpa only [hw.2.1] using hG
    apply w.sound hw (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (by simpa only [hi] using coded_exact p i)
      (natAuxOwners p 0 i) (natAuxOwners p 1 i)
    · exact single_actual family w.first.val w.first.property 0
        hw.2.2.1 hF' p i hf (hi.trans hw.1.symm)
    · exact single_actual family w.second.val w.second.property 1
        hw.2.2.2.1 hG' p i hf (hi.trans hw.2.1.symm)
    · exact nat_combined_exact p i⟩

/-- Extend a permutation only to state the finite output map. All semantic
uses below prove that the input lies in the original ten-point range. -/
def extend (perm : Fin 10 ≃ Fin 10) (n : Nat) : Nat :=
  if h : n < 10 then (perm ⟨n,h⟩).val else n

def pushOwners (perm : Fin 10 ≃ Fin 10) (owned : Finset Nat) : Finset Nat :=
  owned.image (extend perm)

def pulledOwners (perm : Fin 10 ≃ Fin 10) (owned : Finset (Fin 10)) : Finset Nat :=
  (owned.image perm.symm).image Fin.val

private theorem mem_values (owned : Finset (Fin 10)) (j : Fin 10) :
    j.val ∈ owned.image Fin.val ↔ j ∈ owned := by
  constructor
  · intro h
    obtain ⟨k,hk,equal⟩ := Finset.mem_image.mp h
    exact (Fin.val_injective equal) ▸ hk
  · intro h
    exact Finset.mem_image.mpr ⟨j,h,rfl⟩

theorem mem_pulled (perm : Fin 10 ≃ Fin 10) (owned : Finset (Fin 10)) (j : Fin 10) :
    j.val ∈ pulledOwners perm owned ↔ perm j ∈ owned := by
  rw [pulledOwners, mem_values]
  constructor
  · intro h
    obtain ⟨k,hk,equal⟩ := Finset.mem_image.mp h
    have he : k = perm j := by
      calc k = perm (perm.symm k) := (perm.apply_symm_apply k).symm
           _ = perm j := congrArg perm equal
    exact he ▸ hk
  · intro h
    exact Finset.mem_image.mpr ⟨perm j,h,perm.symm_apply_apply j⟩

theorem pulled_subset (perm : Fin 10 ≃ Fin 10) (owned : Finset (Fin 10)) :
    pulledOwners perm owned ⊆ Finset.range 10 := by
  intro n hn
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hn
  exact Finset.mem_range.mpr j.isLt

theorem pulled_card (perm : Fin 10 ≃ Fin 10) (owned : Finset (Fin 10)) :
    (pulledOwners perm owned).card = owned.card := by
  unfold pulledOwners
  rw [Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ perm.symm.injective]

theorem push_pulled (perm : Fin 10 ≃ Fin 10) (owned : Finset (Fin 10)) :
    pushOwners perm (pulledOwners perm owned) = owned.image Fin.val := by
  simp only [pushOwners, pulledOwners, Finset.image_image]
  apply Finset.image_congr
  intro j _
  change extend perm (perm.symm j).val = j.val
  rw [extend, dif_pos (perm.symm j).isLt]
  exact congrArg Fin.val (perm.apply_symm_apply j)

theorem pull_exact (t : Transform) (q : OpenSquare) (k : Fin 2)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10, t.applyRat ((auxPoints (auxKind k))[j.val]!) =
      (auxPoints (auxKind k))[(perm j).val]!)
    (owned : Finset (Fin 10))
    (actual : AuxExact q (auxKind k) (owned.image Fin.val)) :
    AuxExact (t.pull q) (auxKind k) (pulledOwners perm owned) := by
  intro j hj
  have jlt : j < 10 := by simpa only [aux_kind_length] using List.mem_range.mp hj
  let J : Fin 10 := ⟨j,jlt⟩
  rw [rat_inside_transform]
  have point := points J
  change t.applyRat ((auxPoints (auxKind k))[j]!) =
    (auxPoints (auxKind k))[(perm J).val]! at point
  rw [point, actual (perm J).val
    (by simpa only [aux_kind_length] using List.mem_range.mpr (perm J).isLt)]
  change (perm J).val ∈ owned.image Fin.val ↔ J.val ∈ pulledOwners perm owned
  rw [mem_values, mem_pulled]

/-- Transport every possible complete owner set, with its cardinality intact.
The output coverage premise ranges over the checked source specification's
small allowed lists, not all subsets of the twenty auxiliary points. -/
def ofTransformedCombined (family : Finset Nat) (mask : Nat)
    (t : Transform) (ht : t ∈ allTransforms)
    (w : CombinedSpec) (hw : w.Check)
    (hm : w.mask ∈ candidateMasks) (hmask : t.maskAction w.mask = mask)
    (permF permG : Fin 10 ≃ Fin 10)
    (pointF : ∀ j : Fin 10, t.applyRat ((auxPoints 0)[j.val]!) =
      (auxPoints 0)[(permF j).val]!)
    (pointG : ∀ j : Fin 10, t.applyRat ((auxPoints 1)[j.val]!) =
      (auxPoints 1)[(permG j).val]!)
    (hF : Bounds family mask w.first.val 0)
    (hG : Bounds family mask w.second.val 1)
    (allowed : List (Finset Nat))
    (hallowed : ∀ x ∈ w.first.val.allowed, ∀ y ∈ w.second.val.allowed,
      combinedOwners x y ∈ w.allowed →
      combinedOwners (pushOwners permF x) (pushOwners permG y) ∈ allowed) :
    CertifiedDomain family :=
  ⟨mask, allowed, by
    intro p i hf hi
    let x := pulledOwners permF (sortedAuxOwners p 0 i)
    let y := pulledOwners permG (sortedAuxOwners p 1 i)
    have hxcard : x.card = (natAuxOwners p 0 i).card :=
      (pulled_card permF _).trans (nat_aux_card p 0 i).symm
    have hycard : y.card = (natAuxOwners p 1 i).card :=
      (pulled_card permG _).trans (nat_aux_card p 1 i).symm
    have hxb := actual_bounds family mask w.first.val 0 hF p i hf hi
    have hyb := actual_bounds family mask w.second.val 1 hG p i hf hi
    rw [← hxcard] at hxb
    rw [← hycard] at hyb
    have hmarkers := exact_markers_pull t ht (p.square i) w.mask hm
      (by simpa only [hmask, hi] using coded_exact p i)
    have ha : 1 < (t.pull (p.square i)).side := by
      simpa only [pull_same_side, p.congruent] using p.side_gt_one
    have hsize : (t.pull (p.square i)).side ≤ 1001/1000 := by
      simpa only [pull_same_side, p.congruent] using p.side_le
    have box := container_transform t (p.square i) (p.contained i)
    have hx : AuxExact (t.pull (p.square i)) 0 x :=
      pull_exact t (p.square i) 0 permF pointF _ (nat_aux_exact p 0 i)
    have hy : AuxExact (t.pull (p.square i)) 1 y :=
      pull_exact t (p.square i) 1 permG pointG _ (nat_aux_exact p 1 i)
    have hxs : x ⊆ Finset.range 10 := pulled_subset permF _
    have hys : y ⊆ Finset.range 10 := pulled_subset permG _
    have xallowed := w.first.val.sound w.first.property _ ha hsize box
      (by simpa only [hw.1] using hmarkers) x
      (by simpa only [hw.2.2.1] using hx) hxs hxb.1 hxb.2
    have yallowed := w.second.val.sound w.second.property _ ha hsize box
      (by simpa only [hw.2.1] using hmarkers) y
      (by simpa only [hw.2.2.2.1] using hy) hys hyb.1 hyb.2
    have combined := w.sound hw _ ha hsize box hmarkers x y xallowed yallowed
      (combined_exact _ _ _ hxs hx hy)
    have result := hallowed x xallowed y yallowed combined
    dsimp only [x,y] at result
    simpa only [push_pulled, natAuxOwners, natCombinedOwners] using result⟩

def reflectXF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![8,9,6,7,4,5,2,3,0,1] (by decide +kernel)

def reflectXG : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![8,9,5,6,7,2,3,4,0,1] (by decide +kernel)

theorem reflectXF_points (j : Fin 10) :
    (⟨false,true,false⟩ : Transform).applyRat ((auxPoints 0)[j.val]!) =
      (auxPoints 0)[(reflectXF j).val]! := by
  fin_cases j <;> decide +kernel

theorem reflectXG_points (j : Fin 10) :
    (⟨false,true,false⟩ : Transform).applyRat ((auxPoints 1)[j.val]!) =
      (auxPoints 1)[(reflectXG j).val]! := by
  fin_cases j <;> decide +kernel

/-- A half-turn reverses both original ten-point auxiliary lists. -/
def halfTurnPerm : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![9,8,7,6,5,4,3,2,1,0] (by decide +kernel)

theorem halfTurnF_points (j : Fin 10) :
    (⟨false,true,true⟩ : Transform).applyRat ((auxPoints 0)[j.val]!) =
      (auxPoints 0)[(halfTurnPerm j).val]! := by
  fin_cases j <;> decide +kernel

theorem halfTurnG_points (j : Fin 10) :
    (⟨false,true,true⟩ : Transform).applyRat ((auxPoints 1)[j.val]!) =
      (auxPoints 1)[(halfTurnPerm j).val]! := by
  fin_cases j <;> decide +kernel

#print axioms ofCombined
#print axioms ofTransformedCombined

end
end N12Compact.RelaxedOwnerDomain
