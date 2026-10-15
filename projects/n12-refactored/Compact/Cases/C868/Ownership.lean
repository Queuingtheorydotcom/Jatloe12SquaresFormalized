import Compact.Cases.MergedLower.Helpers
import Compact.Bridge.ForcedAuxiliary

/-! Nine original ownership domains, not the archived refined vector list.
The right wall keeps its full two-point G budget; the lower-left central owner
is required to contain two points but may retain an additional G point. -/
namespace N12Compact.C868
open S12 S12Pilot OwnerBudget RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

def family : Finset Nat := {1,2,12,16,192,256,512,3072,4096,8192,16416,32768}

private def domain1 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain2 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec3 combinedSpec3_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain16 : CertifiedDomain family :=
  MergedLower.halfturned family 16 combinedSpec1 combinedSpec1_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain4096 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec17 combinedSpec17_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain8192 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec19 combinedSpec19_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain16416 : CertifiedDomain family :=
  OwnerBudget.product family 16416
    (HalfDomain.ofSeedHull family 16416 0 9 (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      ⟨(3,9/4),(3,11/4),(3,9/4),(3,113/50),1/50,0⟩
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (ofSmallBudgetWithSeed family 16416 1 (by decide +kernel) 9 (by decide +kernel)
      ⟨(3,9/4),(3,11/4),(3,9/4),(3,12/5),3/10,0⟩
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel))

private def domain32768 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec24 combinedSpec24_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain256 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec6 combinedSpec6_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

private def domain512 : CertifiedDomain family :=
  MergedLower.direct family combinedSpec8 combinedSpec8_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def domains : List (CertifiedDomain family) :=
  [domain1,domain2,domain16,domain4096,domain8192,domain16416,
    domain32768,domain256,domain512]

theorem domains_members : ∀ d ∈ domains, d.mask ∈ family := by decide +kernel
theorem domains_distinct : domains.Pairwise (fun a b => a.mask ≠ b.mask) := by
  decide +kernel

/-- Only these forced memberships are used by the current geometric ending. -/
def pointClaims : Fin 7 → Nat × Nat :=
  ![(256,4),(256,13),(32768,14),(1,2),(2,10),(1,12),(2,0)]

theorem pointClaims_checked (i : Fin 7) :
    feasible (ForcedAuxiliary.withoutPoint domains (pointClaims i).1
      (pointClaims i).2) ∅ = false := by
  fin_cases i <;> decide +kernel

theorem forced_point (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 7) : (pointClaims i).2 ∈
      natCombinedOwners p (ownerIndex p (pointClaims i).1) :=
  ForcedAuxiliary.contains domains domains_members domains_distinct
    (pointClaims i).1 (pointClaims i).2 (pointClaims_checked i) p hf

noncomputable def owner (p : NormalizedPacking) (mask : Nat) : OpenSquare :=
  p.square (ownerIndex p mask)

theorem seed_inside (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (mask : Nat) (hm : mask ∈ family) (P : ℚ × ℚ)
    (hp : P ∈ seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 := by
  have code := ownerIndex_spec p mask (by rw [hf]; exact hm)
  exact seed_points_sound _
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    _ (by simpa only [code] using coded_exact p (ownerIndex p mask)) P hp

theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (mask other : Nat) (hm : mask ∈ family) (ho : other ∈ family)
    (hne : mask ≠ other) :
    ∀ x y, ¬ ((owner p mask).Inside x y ∧ (owner p other).Inside x y) := by
  apply p.disjoint
  intro equal
  have h1 := ownerIndex_spec p mask (by rw [hf]; exact hm)
  have h2 := ownerIndex_spec p other (by rw [hf]; exact ho)
  exact hne (h1.symm.trans ((congrArg (markerCode p) equal).trans h2))

theorem forced_inside (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i : Fin 7) :
    (owner p (pointClaims i).1).Inside
      ((auxPoints 2)[(pointClaims i).2]!).1 ((auxPoints 2)[(pointClaims i).2]!).2 :=
  (nat_combined_exact p (ownerIndex p (pointClaims i).1) (pointClaims i).2
    (by fin_cases i <;> decide +kernel)).mpr (forced_point p hf i)

end
end N12Compact.C868
