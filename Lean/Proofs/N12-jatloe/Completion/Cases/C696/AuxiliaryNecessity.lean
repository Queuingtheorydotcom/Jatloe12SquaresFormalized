import Completion.Cases.C696.SideSignPacking
import Completion.Cases.C696.AuxUnique
import S12.DomainSpecData
import S12.SpecPacking

/-!
The original certified single-family domains imply the returned unique C696
assignment. No local geometric search is repeated: `SingleSpec.actual` supplies
the necessary domains, actual packing disjointness supplies injectivity, and
the returned forced-matching proof fixes the twenty singleton sets. The two
corner-pair owners have empty auxiliary sets by the original packing budget.

`DomainSpecData` is existing certified baseline data. This module introduces
no native checks; its new finite checks only bind that data to this family.
The proof inherits the original `native_decide` trust of the imported checked
SingleSpecs and their existing geometric dependencies.
-/

namespace S12Completion.C696.AuxiliaryNecessity
open S12 S12Pilot SideSignPacking

/-- Original owners other than the two exempt corner pairs. -/
def nonexempt : Fin 10 → Fin 12 := ![0, 1, 3, 4, 6, 7, 8, 9, 10, 11]

theorem nonexempt_injective : Function.Injective nonexempt := by decide
theorem ownerMasks_injective : Function.Injective ownerMasks := by decide

def candidates : Fin 2 → Fin 10 → List Nat := ![
  ![[2], [0], [7], [9], [0, 2, 4], [5, 7, 9], [0, 1], [2, 4, 6], [8, 9], [3, 5, 7]],
  ![[2], [0], [7], [9], [0, 2, 3], [6, 7, 9], [0, 1, 3], [2, 5], [6, 8, 9], [4, 7]]]

def assigned : Fin 2 → Fin 10 → Nat := ![
  ![2, 0, 7, 9, 4, 5, 1, 6, 8, 3],
  ![2, 0, 7, 9, 3, 6, 1, 5, 8, 4]]

/-- Existing geometric certificates, in exactly the same owner/family order. -/
def specifications : Fin 2 → Fin 10 → {w : SingleSpec // w.Check} := ![
  ![⟨singleSpec0, singleSpec0_checked⟩, ⟨singleSpec4, singleSpec4_checked⟩,
    ⟨singleSpec14, singleSpec14_checked⟩, ⟨singleSpec17, singleSpec17_checked⟩,
    ⟨singleSpec20, singleSpec20_checked⟩, ⟨singleSpec34, singleSpec34_checked⟩,
    ⟨singleSpec55, singleSpec55_checked⟩, ⟨singleSpec66, singleSpec66_checked⟩,
    ⟨singleSpec75, singleSpec75_checked⟩, ⟨singleSpec88, singleSpec88_checked⟩],
  ![⟨singleSpec2, singleSpec2_checked⟩, ⟨singleSpec6, singleSpec6_checked⟩,
    ⟨singleSpec16, singleSpec16_checked⟩, ⟨singleSpec18, singleSpec18_checked⟩,
    ⟨singleSpec22, singleSpec22_checked⟩, ⟨singleSpec35, singleSpec35_checked⟩,
    ⟨singleSpec57, singleSpec57_checked⟩, ⟨singleSpec68, singleSpec68_checked⟩,
    ⟨singleSpec77, singleSpec77_checked⟩, ⟨singleSpec90, singleSpec90_checked⟩]]

theorem specifications_checked : ∀ k j,
    (specifications k j).val.mask = ownerMasks (nonexempt j) ∧
    (specifications k j).val.Matches family k ∧
    (specifications k j).val.allowed =
      (candidates k j).map (fun n => ({n} : Finset Nat)) := by
  decide

noncomputable def actual (p : NormalizedPacking) (k : Fin 2) (i : Fin 12) :
    Finset Nat := natAuxOwners p k (ownerIndex p (ownerMasks i))

private theorem marker_code (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    markerCode p (ownerIndex p (ownerMasks i)) = ownerMasks i :=
  ownerIndex_spec p _ (by rw [hf]; exact ownerMasks_mem i)

theorem actual_domains (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (j : Fin 10) :
    actual p k (nonexempt j) ∈ (candidates k j).map (fun n => ({n} : Finset Nat)) := by
  obtain ⟨hm, hmatch, hallowed⟩ := specifications_checked k j
  have h := (specifications k j).val.actual (specifications k j).property family k
    hmatch p (ownerIndex p (ownerMasks (nonexempt j))) hf
    ((marker_code p hf (nonexempt j)).trans hm.symm)
  simpa only [actual, hallowed] using h

theorem actual_disjoint (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (i j : Fin 12) (hij : i ≠ j) :
    Disjoint (actual p k i) (actual p k j) := by
  apply nat_aux_disjoint
  intro he
  apply hij
  apply ownerMasks_injective
  exact (marker_code p hf i).symm.trans
    ((congrArg (markerCode p) he).trans (marker_code p hf j))

theorem singleton_exists (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (j : Fin 10) :
    ∃ n, n ∈ candidates k j ∧ actual p k (nonexempt j) = {n} := by
  obtain ⟨n, hn, he⟩ := List.mem_map.mp (actual_domains p hf k j)
  exact ⟨n, hn, he.symm⟩

noncomputable def chosen (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (j : Fin 10) : Nat :=
  Classical.choose (singleton_exists p hf k j)

theorem chosen_spec (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (j : Fin 10) :
    chosen p hf k j ∈ candidates k j ∧
      actual p k (nonexempt j) = {chosen p hf k j} :=
  Classical.choose_spec (singleton_exists p hf k j)

/-- Extend the ten certified choices to the returned theorem's Nat interface. -/
noncomputable def selection (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (j : Nat) : Nat :=
  if hj : j < 10 then chosen p hf k ⟨j, hj⟩ else 0

theorem selection_spec (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (j : Fin 10) :
    selection p hf k j ∈ candidates k j ∧
      actual p k (nonexempt j) = {selection p hf k j} := by
  simpa only [selection, dif_pos j.isLt] using chosen_spec p hf k j

theorem selection_distinct (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) : C696Aux.Distinct10 (selection p hf k) := by
  intro i hi j hj hij he
  have hne : nonexempt ⟨i, hi⟩ ≠ nonexempt ⟨j, hj⟩ := by
    intro h
    exact hij (congrArg Fin.val (nonexempt_injective h))
  have hd := actual_disjoint p hf k (nonexempt ⟨i, hi⟩) (nonexempt ⟨j, hj⟩) hne
  have hm : selection p hf k i ∈ actual p k (nonexempt ⟨i, hi⟩) := by
    rw [(selection_spec p hf k ⟨i, hi⟩).2]
    exact Finset.mem_singleton_self _
  have hn : selection p hf k i ∈ actual p k (nonexempt ⟨j, hj⟩) := by
    rw [(selection_spec p hf k ⟨j, hj⟩).2, he]
    exact Finset.mem_singleton_self _
  exact Finset.disjoint_left.mp hd hm hn

private theorem f_domain_iff (f : Nat → Nat) :
    C696Aux.FDomain f ↔ ∀ j : Fin 10, f j ∈ candidates 0 j := by
  simp [C696Aux.FDomain, candidates, Fin.forall_fin_succ]

private theorem g_domain_iff (g : Nat → Nat) :
    C696Aux.GDomain g ↔ ∀ j : Fin 10, g j ∈ candidates 1 j := by
  simp [C696Aux.GDomain, candidates, Fin.forall_fin_succ]

private theorem f_assignment_iff (f : Nat → Nat) :
    C696Aux.FAssignment f ↔ ∀ j : Fin 10, f j = assigned 0 j := by
  simp [C696Aux.FAssignment, assigned, Fin.forall_fin_succ]

private theorem g_assignment_iff (g : Nat → Nat) :
    C696Aux.GAssignment g ↔ ∀ j : Fin 10, g j = assigned 1 j := by
  simp [C696Aux.GAssignment, assigned, Fin.forall_fin_succ]

theorem actual_singletons (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    ∀ k j, actual p k (nonexempt j) = {assigned k j} := by
  have hfdom : C696Aux.FDomain (selection p hf 0) :=
    (f_domain_iff _).mpr (fun j => (selection_spec p hf 0 j).1)
  have hgdom : C696Aux.GDomain (selection p hf 1) :=
    (g_domain_iff _).mpr (fun j => (selection_spec p hf 1 j).1)
  have hF := (f_assignment_iff _).mp
    (C696Aux.f_unique _ hfdom (selection_distinct p hf 0))
  have hG := (g_assignment_iff _).mp
    (C696Aux.g_unique _ hgdom (selection_distinct p hf 1))
  intro k j
  fin_cases k
  · change actual p 0 (nonexempt j) = {assigned 0 j}
    rw [(selection_spec p hf 0 j).2, hF j]
  · change actual p 1 (nonexempt j) = {assigned 1 j}
    rw [(selection_spec p hf 1 j).2, hG j]

theorem actual_empty (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (k : Fin 2) (i : Fin 12) (hi : i = 2 ∨ i = 5) : actual p k i = ∅ := by
  have hb := (nat_aux_budget p k (ownerIndex p (ownerMasks i))).2
  rw [hf, marker_code p hf i] at hb
  have hz : (family ∩ auxExempt k).card - 2 +
      (if ownerMasks i ∈ auxExempt k then 0 else 1) = 0 := by
    rcases hi with rfl | rfl <;> fin_cases k <;> decide
  apply Finset.card_eq_zero.mp
  apply Nat.eq_zero_of_le_zero
  simpa only [actual, hz] using hb

/-- Every actual packing with the original C696 marker family has exactly the
returned complete F/G assignment. There is no residual ownership premise. -/
theorem exact_assignment (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    ExactAssignment p := by
  have hs := actual_singletons p hf
  have he := actual_empty p hf
  intro i
  change combinedOwners (actual p 0 i) (actual p 1 i) = auxiliaryVector i
  fin_cases i
  · erw [hs 0 0, hs 1 0]; decide
  · erw [hs 0 1, hs 1 1]; decide
  · erw [he 0 2 (Or.inl rfl), he 1 2 (Or.inl rfl)]; decide
  · erw [hs 0 2, hs 1 2]; decide
  · erw [hs 0 3, hs 1 3]; decide
  · erw [he 0 5 (Or.inr rfl), he 1 5 (Or.inr rfl)]; decide
  · erw [hs 0 4, hs 1 4]; decide
  · erw [hs 0 5, hs 1 5]; decide
  · erw [hs 0 6, hs 1 6]; decide
  · erw [hs 0 7, hs 1 7]; decide
  · erw [hs 0 8, hs 1 8]; decide
  · erw [hs 0 9, hs 1 9]; decide

theorem ownership_vector (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    ownershipVector p = List.ofFn auxiliaryVector :=
  congrArg (fun f : Fin 12 → Finset Nat => List.ofFn f)
    (funext (exact_assignment p hf))

/-- All four strict side signs now follow from the original family alone. -/
theorem center_signs (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    2 < centerY (owners p 8) ∧ 2 < centerX (owners p 9) ∧
      centerY (owners p 10) < 2 ∧ centerX (owners p 11) < 2 :=
  SideSignPacking.center_signs p hf (exact_assignment p hf)

theorem center_signs_of_row (r : S12.CoverRow) (hr : r ∈ retainedRows)
    (hid : r.originalId = 696) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = r.groups) :
    2 < centerY (owners p 8) ∧ 2 < centerX (owners p 9) ∧
      centerY (owners p 10) < 2 ∧ centerX (owners p 11) < 2 :=
  center_signs p (hf.trans (row_family r hr hid))

#print axioms exact_assignment
#print axioms center_signs_of_row
end S12Completion.C696.AuxiliaryNecessity
