import Compact.Completion.OtherCases.MonotoneQueries

/-! Compact full-owner filters from certified local queries and actual
strict-point diameter. No joint ownership vectors are enumerated. -/
namespace N12Compact.Completion.OtherCases.MonotoneQueries
open S12 S12Pilot
set_option Elab.async false

def compatibleCombined (entry : Signature) (mask : Nat) (owned : Finset Nat) : Prop :=
  entry.1=mask ∧ entry.2.1=2 ∧ entry.2.2.1 ⊆ owned ∧ Disjoint owned entry.2.2.2

instance (entry : Signature) (mask : Nat) (owned : Finset Nat) :
    Decidable (compatibleCombined entry mask owned) := by
  unfold compatibleCombined
  infer_instance

def trim {family : Finset Nat} (domain : CertifiedDomain family)
    (queries : List {query : LocalQuery // query.Check}) (signatures : List Signature)
    (exactSignatures : signatures=queries.map (fun q => signature q.val)) :
    CertifiedDomain family :=
  ⟨domain.mask,domain.allowed.filter (fun owned =>
      decide (¬∃ entry∈signatures,compatibleCombined entry domain.mask owned)),by
    classical
    intro p i familyExact maskExact
    apply List.mem_filter.mpr
    refine ⟨domain.sound p i familyExact maskExact,decide_eq_true ?_⟩
    rintro ⟨entry,member,hm,hk,anchors,missing⟩
    rw [exactSignatures] at member
    obtain ⟨query,_,equal⟩ := List.mem_map.mp member
    subst entry
    change query.val.mask=domain.mask at hm
    change query.val.kind=2 at hk
    change query.val.owned⊆natCombinedOwners p i at anchors
    change Disjoint (natCombinedOwners p i) (blocked query.val) at missing
    exact extended_sound query.val query.property _ anchors missing (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (by simpa only [hm,maskExact] using coded_exact p i)
      (by simpa only [hk] using nat_combined_exact p i)⟩

def diameterCheck (mask : Nat) (owned : Finset Nat) : Prop :=
  ∀ x∈queryInsidePoints mask 2 owned, ∀ y∈queryInsidePoints mask 2 owned,
    distSq x y < 2*(1001/1000 : ℚ)^2

instance (mask : Nat) (owned : Finset Nat) : Decidable (diameterCheck mask owned) := by
  unfold diameterCheck
  let points := queryInsidePoints mask 2 owned
  letI (x : ℚ × ℚ) : Decidable (∀ y∈points,distSq x y < 2*(1001/1000 : ℚ)^2) :=
    List.decidableBAll _ points
  exact List.decidableBAll _ points

private theorem actual_diameter (p : NormalizedPacking) (i : Fin 12) (mask : Nat)
    (maskExact : markerCode p i=mask) : diameterCheck mask (natCombinedOwners p i) := by
  have side := p.side_le
  have positive := p.side_gt_one
  have cap : p.commonSide^2 ≤ (1001/1000 : ℝ)^2 := by
    nlinarith only [side,positive]
  have inside := query_inside_sound mask 2 (natCombinedOwners p i) (p.square i)
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained i)
    (by simpa only [maskExact] using coded_exact p i) (nat_combined_exact p i)
  intro x hx y hy
  have distance := inside_distance_bound (p.square i) x.1 x.2 y.1 y.2
    (inside x hx) (inside y hy)
  rw [p.congruent] at distance
  have bound : ((x.1 : ℝ)-y.1)^2+((x.2 : ℝ)-y.2)^2 <
      2*(1001/1000 : ℝ)^2 := by nlinarith only [distance,cap]
  unfold distSq
  apply (Rat.cast_lt (K := ℝ)).mp
  push_cast
  simpa only [pow_two,Rat.cast_mul,Rat.cast_sub,Rat.cast_div,Rat.cast_ofNat] using bound

def diameterFilter {family : Finset Nat} (domain : CertifiedDomain family) :
    CertifiedDomain family :=
  ⟨domain.mask,domain.allowed.filter (fun owned => decide (diameterCheck domain.mask owned)),by
    intro p i familyExact maskExact
    exact List.mem_filter.mpr ⟨domain.sound p i familyExact maskExact,
      decide_eq_true (actual_diameter p i domain.mask maskExact)⟩⟩

#print axioms diameterFilter
end N12Compact.Completion.OtherCases.MonotoneQueries

