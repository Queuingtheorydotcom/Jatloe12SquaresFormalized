import Mathlib.Tactic.DeriveFintype
import Compact.Bridge.OwnerBudget
import S12.DomainSpecData
import S12.Diameter

/-! Original ownership entrances for 697, 698 and 699. Two apparent
assignments of the generic merged-top domain put a point farther from its
strict top marker than the square's diameter; these are removed geometrically
before the small finite ownership check. -/
namespace N12Compact.MergedTopFurther
open S12 S12Pilot OwnerBudget
set_option Elab.async false
set_option maxRecDepth 10000

inductive Variant where
  | base | mergeRight | mergeBottom
  deriving DecidableEq

instance : Fintype Variant where
  elems := {.base, .mergeRight, .mergeBottom}
  complete v := by cases v <;> simp

def bottomMask : Variant → Nat
  | .mergeBottom => 8704
  | _ => 8192

def rightMask : Variant → Nat
  | .mergeRight => 16896
  | _ => 16384

def family (v : Variant) : Finset Nat :=
  {1,2,12,16,32,192,256,1024,4096,bottomMask v,rightMask v,34816}

private def domain1 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec0 combinedSpec0_checked
    (by cases v <;> decide +kernel)

private def domain2 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec2 combinedSpec2_checked
    (by cases v <;> decide +kernel)

private def domain16 (v : Variant) : CertifiedDomain (family v) :=
  OwnerBudget.product (family v) 16
    (HalfDomain.ofSpec (family v) singleSpec14 0 singleSpec14_checked
      (by cases v <;> decide +kernel))
    (HalfDomain.ofSpec (family v) singleSpec16 1 singleSpec16_checked
      (by cases v <;> decide +kernel))

private def domain32 (v : Variant) : CertifiedDomain (family v) :=
  OwnerBudget.product (family v) 32
    (HalfDomain.ofSpec (family v) singleSpec17 0 singleSpec17_checked
      (by cases v <;> decide +kernel))
    (HalfDomain.ofSpec (family v) singleSpec18 1 singleSpec18_checked
      (by cases v <;> decide +kernel))

private def domain256 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec5 combinedSpec5_checked
    (by cases v <;> decide +kernel)

private def domain1024 (v : Variant) : CertifiedDomain (family v) :=
  OwnerBudget.product (family v) 1024
    (HalfDomain.ofSpec (family v) singleSpec34 0 singleSpec34_checked
      (by cases v <;> decide +kernel))
    (HalfDomain.ofSpec (family v) singleSpec35 1 singleSpec35_checked
      (by cases v <;> decide +kernel))

private def domain4096 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec16 combinedSpec16_checked
    (by cases v <;> decide +kernel)

private def domainBottom : (v : Variant) → CertifiedDomain (family v)
  | .base => CertifiedDomain.ofCombined (family .base) combinedSpec18
      combinedSpec18_checked (by decide +kernel)
  | .mergeRight => CertifiedDomain.ofCombined (family .mergeRight) combinedSpec18
      combinedSpec18_checked (by decide +kernel)
  | .mergeBottom => OwnerBudget.product (family .mergeBottom) 8704
      (HalfDomain.ofSpec (family .mergeBottom) singleSpec74 0 singleSpec74_checked
        (by decide +kernel))
      (HalfDomain.singleton (family .mergeBottom) 8704 1
        (by decide +kernel) (by decide +kernel))

private def domainRight : (v : Variant) → CertifiedDomain (family v)
  | .base => CertifiedDomain.ofCombined (family .base) combinedSpec20
      combinedSpec20_checked (by decide +kernel)
  | .mergeBottom => CertifiedDomain.ofCombined (family .mergeBottom) combinedSpec20
      combinedSpec20_checked (by decide +kernel)
  | .mergeRight => OwnerBudget.product (family .mergeRight) 16896
      (HalfDomain.ofSpec (family .mergeRight) singleSpec85 0 singleSpec85_checked
        (by decide +kernel))
      (HalfDomain.singleton (family .mergeRight) 16896 1
        (by decide +kernel) (by decide +kernel))

private def mergedTopBudget (v : Variant) : CertifiedDomain (family v) :=
  OwnerBudget.product (family v) 34816
    (HalfDomain.singleton (family v) 34816 0
      (by cases v <;> decide +kernel) (by decide +kernel))
    (HalfDomain.singleton (family v) 34816 1
      (by cases v <;> decide +kernel) (by decide +kernel))

/-- This excludes auxiliary indices 15 and 18 for every actual merged-top
square, independently of all the other auxiliary assignments. -/
private theorem merged_top_diameter (p : NormalizedPacking) (i : Fin 12)
    (code : markerCode p i = 34816) :
    15 ∉ natCombinedOwners p i ∧ 18 ∉ natCombinedOwners p i := by
  have high : (p.square i).Inside 2 (1543/500) := by
    have point := seed_points_sound (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i)
      (maskSupport 34816) (by simpa only [code] using coded_exact p i)
      (2,1543/500) (by decide +kernel)
    simpa using point
  have size : (p.square i).side ≤ 1001/1000 := by
    rw [p.congruent]; exact p.side_le
  constructor
  · intro member
    have point := (nat_combined_exact p i 15 (by decide +kernel)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at point
    have bound := normalized_diameter_bound (p.square i) size
      2 (1543/500) (113/50) 1 high point
    norm_num at bound
  · intro member
    have point := (nat_combined_exact p i 18 (by decide +kernel)).mpr member
    norm_num [auxPoints,fPoints,gPoints] at point
    have bound := normalized_diameter_bound (p.square i) size
      2 (1543/500) 3 (8/5) high point
    norm_num at bound

private def domain34816 (v : Variant) : CertifiedDomain (family v) :=
  ⟨34816,(mergedTopBudget v).allowed.filter
    (fun s => decide (15 ∉ s ∧ 18 ∉ s)),by
    intro p i hf hi
    apply List.mem_filter.mpr
    exact ⟨(mergedTopBudget v).sound p i hf hi,
      decide_eq_true (merged_top_diameter p i hi)⟩⟩

def domains (v : Variant) : List (CertifiedDomain (family v)) :=
  [domain1 v,domain2 v,domain16 v,domain32 v,domain256 v,
    domain1024 v,domain4096 v,domainBottom v,domainRight v,domain34816 v]

theorem domains_members (v : Variant) : ∀ d ∈ domains v, d.mask ∈ family v := by
  cases v <;> decide +kernel

theorem domains_distinct (v : Variant) :
    (domains v).Pairwise (fun a b => a.mask ≠ b.mask) := by
  cases v <;> decide +kernel

def masks (v : Variant) : Fin 10 → Nat :=
  ![1,2,16,32,256,1024,4096,bottomMask v,rightMask v,34816]

def owned : Fin 10 → Finset Nat :=
  ![{2,12},{0,10},{7,17},{9,19},{4,13},{5,16},{1,11},{6,15},{8,18},{3,14}]

theorem forced_checked (v : Variant) (i : Fin 10) :
    feasible (forcedDomains (domains v) (masks v i) (owned i)) ∅ = false := by
  cases v <;> fin_cases i <;> decide +kernel

theorem forced (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 10) :
    natCombinedOwners p (ownerIndex p (masks v i)) = owned i :=
  certified_domain_forced (domains v) (domains_members v) (domains_distinct v)
    (masks v i) (owned i) (forced_checked v i) p hf

noncomputable def owner (v : Variant) (p : NormalizedPacking) (i : Fin 10) : OpenSquare :=
  p.square (ownerIndex p (masks v i))

theorem owner_code (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 10) :
    markerCode p (ownerIndex p (masks v i)) = masks v i :=
  ownerIndex_spec p _ (by rw [hf]; cases v <;> fin_cases i <;> decide +kernel)

theorem inside (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 10) (P : ℚ × ℚ)
    (hp : P ∈ queryInsidePoints (masks v i) 2 (owned i)) :
    (owner v p i).Inside P.1 P.2 := by
  have aux : AuxExact (owner v p i) 2 (owned i) := by
    simpa only [owner,forced v p hf i] using nat_combined_exact p (ownerIndex p (masks v i))
  exact query_inside_sound _ 2 _ _
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le)
    (p.contained _) (by simpa only [owner,owner_code v p hf i] using coded_exact p (ownerIndex p (masks v i))) aux P hp

theorem outside (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 10) (P : ℚ × ℚ)
    (hp : P ∈ queryOutsidePoints (masks v i) 2 (owned i)) :
    ¬ (owner v p i).Inside P.1 P.2 := by
  have aux : AuxExact (owner v p i) 2 (owned i) := by
    simpa only [owner,forced v p hf i] using nat_combined_exact p (ownerIndex p (masks v i))
  exact query_outside_sound _ 2 _ _
    (by simpa only [owner,owner_code v p hf i] using coded_exact p (ownerIndex p (masks v i))) aux P hp

theorem apart (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i j : Fin 10) (hne : i ≠ j) :
    ∀ x y, ¬ ((owner v p i).Inside x y ∧ (owner v p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have injective : Function.Injective (masks v) := by cases v <;> decide +kernel
  exact hne (injective ((owner_code v p hf i).symm.trans
    ((congrArg (markerCode p) equal).trans (owner_code v p hf j))))

theorem seed_inside (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (mask : Nat) (hm : mask ∈ family v)
    (P : ℚ × ℚ) (hp : P ∈ seedPoints (maskSupport mask)) :
    (p.square (ownerIndex p mask)).Inside P.1 P.2 := by
  have code := ownerIndex_spec p mask (by rw [hf]; exact hm)
  exact seed_points_sound _
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    _ (by simpa only [code] using coded_exact p (ownerIndex p mask)) P hp

theorem owner_apart_mask (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 10) (mask : Nat)
    (hm : mask ∈ family v) (hne : masks v i ≠ mask) :
    ∀ x y, ¬ ((owner v p i).Inside x y ∧
      (p.square (ownerIndex p mask)).Inside x y) := by
  apply p.disjoint
  intro equal
  have code := ownerIndex_spec p mask (by rw [hf]; exact hm)
  exact hne ((owner_code v p hf i).symm.trans
    ((congrArg (markerCode p) equal).trans code))

#print axioms forced
end N12Compact.MergedTopFurther
