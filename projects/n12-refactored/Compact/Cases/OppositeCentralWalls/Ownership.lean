import Compact.Bridge.OwnerBudget
import S12.DomainSpecData

/-! Eight original families force the same six central and wall owners.
Assignments of the other squares are retained only as consistency constraints;
in particular the two assignments in case 1077 need no geometric subdivision. -/
namespace N12Compact.OppositeCentralWalls
open S12 S12Pilot OwnerBudget
set_option Elab.async false
set_option maxRecDepth 10000

inductive Variant where
  | c709 | c882 | c890 | c1075 | c1077 | c1078 | c1081 | c1083
  deriving DecidableEq, Fintype

def lowMask : Variant → Nat
  | .c709 | .c882 | .c890 => 2
  | .c1077 | .c1083 => 258
  | _ => 256

def cornerMask : Variant → Nat
  | .c1078 | .c1081 | .c1083 => 32
  | _ => 16

def middleMask : Variant → Nat
  | .c709 => 32
  | .c882 | .c1078 => 1024
  | .c1081 | .c1083 => 1040
  | _ => 1056

def family (v : Variant) : Finset Nat :=
  {1,lowMask v,12,cornerMask v,192,512,middleMask v,2048,4096,8192,16384,32768}

private def domain1 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec0 combinedSpec0_checked
    (by cases v <;> decide +kernel)

private def domainLow : (v : Variant) → CertifiedDomain (family v)
  | .c709 => CertifiedDomain.ofCombined (family .c709) combinedSpec2
      combinedSpec2_checked (by decide +kernel)
  | .c882 => CertifiedDomain.ofCombined (family .c882) combinedSpec2
      combinedSpec2_checked (by decide +kernel)
  | .c890 => CertifiedDomain.ofCombined (family .c890) combinedSpec2
      combinedSpec2_checked (by decide +kernel)
  | .c1075 => CertifiedDomain.ofCombined (family .c1075) combinedSpec5
      combinedSpec5_checked (by decide +kernel)
  | .c1078 => CertifiedDomain.ofCombined (family .c1078) combinedSpec5
      combinedSpec5_checked (by decide +kernel)
  | .c1081 => CertifiedDomain.ofCombined (family .c1081) combinedSpec5
      combinedSpec5_checked (by decide +kernel)
  | .c1077 => OwnerBudget.product (family .c1077) 258
      (HalfDomain.ofSpec (family .c1077) singleSpec24 0 singleSpec24_checked
        (by decide +kernel))
      (HalfDomain.singleton (family .c1077) 258 1
        (by decide +kernel) (by decide +kernel))
  | .c1083 => OwnerBudget.product (family .c1083) 258
      (HalfDomain.ofSpec (family .c1083) singleSpec24 0 singleSpec24_checked
        (by decide +kernel))
      (HalfDomain.singleton (family .c1083) 258 1
        (by decide +kernel) (by decide +kernel))

private def domainCorner (v : Variant) : CertifiedDomain (family v) := by
  cases v with
  | c709 | c882 | c890 | c1075 | c1077 =>
    exact OwnerBudget.product _ 16
      (HalfDomain.ofSpec _ singleSpec14 0 singleSpec14_checked (by decide +kernel))
      (HalfDomain.ofSpec _ singleSpec16 1 singleSpec16_checked (by decide +kernel))
  | c1078 | c1081 | c1083 =>
    exact OwnerBudget.product _ 32
      (HalfDomain.ofSpec _ singleSpec17 0 singleSpec17_checked (by decide +kernel))
      (HalfDomain.ofSpec _ singleSpec18 1 singleSpec18_checked (by decide +kernel))

private def domain512 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec7 combinedSpec7_checked
    (by cases v <;> decide +kernel)

private def domainMiddle (v : Variant) : CertifiedDomain (family v) := by
  cases v with
  | c709 =>
    exact OwnerBudget.product _ 32
      (HalfDomain.ofSpec _ singleSpec17 0 singleSpec17_checked (by decide +kernel))
      (HalfDomain.ofSpec _ singleSpec18 1 singleSpec18_checked (by decide +kernel))
  | c882 | c1078 =>
    exact OwnerBudget.product _ 1024
      (HalfDomain.ofSpec _ singleSpec34 0 singleSpec34_checked (by decide +kernel))
      (HalfDomain.ofSpec _ singleSpec35 1 singleSpec35_checked (by decide +kernel))
  | c890 | c1075 | c1077 =>
    exact OwnerBudget.product _ 1056
      (HalfDomain.ofSpec _ singleSpec38 0 singleSpec38_checked (by decide +kernel))
      (HalfDomain.singleton _ 1056 1 (by decide +kernel) (by decide +kernel))
  | c1081 | c1083 =>
    exact CertifiedDomain.ofCombined _ combinedSpec10 combinedSpec10_checked
      (by decide +kernel)

private def domain2048 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec12 combinedSpec12_checked
    (by cases v <;> decide +kernel)

private def domain4096 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec16 combinedSpec16_checked
    (by cases v <;> decide +kernel)

private def domain8192 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec18 combinedSpec18_checked
    (by cases v <;> decide +kernel)

private def domain16384 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec20 combinedSpec20_checked
    (by cases v <;> decide +kernel)

private def domain32768 (v : Variant) : CertifiedDomain (family v) :=
  CertifiedDomain.ofCombined (family v) combinedSpec22 combinedSpec22_checked
    (by cases v <;> decide +kernel)

def domains (v : Variant) : List (CertifiedDomain (family v)) :=
  [domain1 v,domainLow v,domainCorner v,domain512 v,domainMiddle v,
    domain2048 v,domain4096 v,domain8192 v,domain16384 v,domain32768 v]

theorem domains_members (v : Variant) : ∀ d ∈ domains v, d.mask ∈ family v := by
  cases v <;> decide +kernel

theorem domains_distinct (v : Variant) :
    (domains v).Pairwise (fun a b => a.mask ≠ b.mask) := by
  cases v <;> decide +kernel

def masks : Fin 6 → Nat := ![512,2048,4096,8192,16384,32768]
def owned : Fin 6 → Finset Nat :=
  ![{4,16},{5,13},{1,11},{6,15},{8,18},{3,14}]

theorem forced_checked (v : Variant) (i : Fin 6) :
    feasible (forcedDomains (domains v) (masks i) (owned i)) ∅ = false := by
  cases v <;> fin_cases i <;> decide +kernel

theorem forced (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 6) :
    natCombinedOwners p (ownerIndex p (masks i)) = owned i :=
  certified_domain_forced (domains v) (domains_members v) (domains_distinct v)
    (masks i) (owned i) (forced_checked v i) p hf

noncomputable def owner (p : NormalizedPacking) (i : Fin 6) : OpenSquare :=
  p.square (ownerIndex p (masks i))

theorem owner_code (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 6) :
    markerCode p (ownerIndex p (masks i)) = masks i :=
  ownerIndex_spec p _ (by rw [hf]; cases v <;> fin_cases i <;> decide +kernel)

theorem inside (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 6) (P : ℚ × ℚ)
    (hp : P ∈ queryInsidePoints (masks i) 2 (owned i)) :
    (owner p i).Inside P.1 P.2 := by
  have aux : AuxExact (owner p i) 2 (owned i) := by
    simpa only [owner,forced v p hf i] using nat_combined_exact p (ownerIndex p (masks i))
  exact query_inside_sound _ 2 _ _
    (by change 1 < (p.square _).side; rw [p.congruent]; exact p.side_gt_one)
    (by change (p.square _).side ≤ 1001/1000; rw [p.congruent]; exact p.side_le)
    (p.contained _) (by simpa only [owner,owner_code v p hf i] using
      coded_exact p (ownerIndex p (masks i))) aux P hp

theorem outside (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i : Fin 6) (P : ℚ × ℚ)
    (hp : P ∈ queryOutsidePoints (masks i) 2 (owned i)) :
    ¬ (owner p i).Inside P.1 P.2 := by
  have aux : AuxExact (owner p i) 2 (owned i) := by
    simpa only [owner,forced v p hf i] using nat_combined_exact p (ownerIndex p (masks i))
  exact query_outside_sound _ 2 _ _
    (by simpa only [owner,owner_code v p hf i] using
      coded_exact p (ownerIndex p (masks i))) aux P hp

theorem apart (v : Variant) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family v) (i j : Fin 6) (hne : i ≠ j) :
    ∀ x y, ¬ ((owner p i).Inside x y ∧ (owner p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have injective : Function.Injective masks := by decide +kernel
  exact hne (injective ((owner_code v p hf i).symm.trans
    ((congrArg (markerCode p) equal).trans (owner_code v p hf j))))

#print axioms forced
end N12Compact.OppositeCentralWalls
