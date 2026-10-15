import Compact.Cases.C868.AdditionalOwnership
import Compact.Geometry.SouthwestCentralReach
import Compact.Completion.OtherCases.ElbowPoint

/-! Actual singleton segments force both southwest crosspoints.  Their
ownership excludes the southeast elbow that omits G8.  All squares below
are the original owners in C868, with no orientation restriction. -/
namespace N12Compact.C868
open S12 S12Pilot
set_option Elab.async false

theorem southwest_crosspoints (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owner p 256).Inside (3/2) 2 ∧ (owner p 256).Inside 2 (3/2) := by
  have size : 1 < (owner p 256).side := by
    rw [show (owner p 256).side = p.commonSide from p.congruent _]
    exact p.side_gt_one
  have marker : (owner p 256).Inside (33/20) (33/20) := by
    simpa using seed_inside p hf 256 (by decide +kernel)
      (33/20,33/20) (by decide +kernel)
  have inward : (owner p 256).Inside 2 (87/50) := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 0
  have upper : (owner p 256).Inside (87/50) 2 := by
    simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 1
  have missing (mask : Nat) (hm : mask ∈ family) (hne : 256 ≠ mask)
      (P : ℚ × ℚ) (hp : P ∈ seedPoints (maskSupport mask)) :
      ¬ (owner p 256).Inside P.1 P.2 := fun own =>
    apart p hf 256 mask (by decide +kernel) hm hne _ _
      ⟨own,seed_inside p hf mask hm P hp⟩
  have ne : ¬(owner p 256).Inside (47/20) (47/20) := by
    simpa using missing 3072 (by decide +kernel) (by decide +kernel)
      (47/20,47/20) (by decide +kernel)
  have nw : ¬(owner p 256).Inside (33/20) (47/20) := by
    simpa using missing 3072 (by decide +kernel) (by decide +kernel)
      (33/20,47/20) (by decide +kernel)
  have se : ¬(owner p 256).Inside (47/20) (33/20) := by
    simpa using missing 512 (by decide +kernel) (by decide +kernel)
      (47/20,33/20) (by decide +kernel)
  constructor
  · exact SouthwestCentralReach.left (owner p 256) (owner p 1) size
      marker inward upper ne nw se
      (by simpa using seed_inside p hf 1 (by decide +kernel)
        (28/25,1) (by decide +kernel))
      (by simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 5)
      (apart p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · exact SouthwestCentralReach.below (owner p 256) (owner p 2) size
      marker inward upper ne nw se
      (by simpa using seed_inside p hf 2 (by decide +kernel)
        (1,28/25) (by decide +kernel))
      (by simpa [pointClaims,auxPoints,fPoints,gPoints] using forced_inside p hf 6)
      (apart p hf 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel))

/-- If B omitted G8, the actual H marker and R marker would put it in
the elbow theorem, forcing the same strict lower crosspoint as A. -/
theorem southeast_g8 (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : (owner p 512).Inside 3 (8/5) := by
  classical
  by_contra missingG
  have elbow := (southeast_g_cover p hf).resolve_right missingG
  have size : 1 < (owner p 512).side := by
    rw [show (owner p 512).side = p.commonSide from p.congruent _]
    exact p.side_gt_one
  have marker : (owner p 512).Inside (47/20) (33/20) := by
    simpa using seed_inside p hf 512 (by decide +kernel)
      (47/20,33/20) (by decide +kernel)
  have outer : (owner p 512).Inside 3 (87/50) := by
    simpa [additionalClaims,auxPoints,fPoints,gPoints] using additional_inside p hf 7
  have missingN : ¬(owner p 512).Inside (47/20) (47/20) := fun own =>
    apart p hf 512 3072 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,by
        simpa using seed_inside p hf 3072 (by decide +kernel)
          (47/20,47/20) (by decide +kernel)⟩
  have missingR : ¬(owner p 512).Inside (1543/500) 2 := fun own =>
    apart p hf 512 16416 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,by
        simpa using seed_inside p hf 16416 (by decide +kernel)
          (1543/500,2) (by decide +kernel)⟩
  have duplicate := Completion.OtherCases.ElbowPoint.points_original
    (owner p 512) size marker elbow outer missingN missingG missingR
  exact apart p hf 256 512 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ ⟨(southwest_crosspoints p hf).2,duplicate.1⟩

#print axioms southwest_crosspoints
#print axioms southeast_g8
end N12Compact.C868
