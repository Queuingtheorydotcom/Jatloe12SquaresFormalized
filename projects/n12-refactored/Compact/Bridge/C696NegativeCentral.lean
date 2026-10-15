import Compact.Bridge.C696CentralReach
import Compact.Geometry.SouthwestNegativeCorner

/-! Original-packing entrance to the complete negative-central sector.
Only the true missing lower-left corner is assumed, as supplied by either
original C696 corner root. No saved enclosure or orientation of a singleton
is inserted. The residual theorem explicitly retains the positive central
sector; it does not claim an unconditional exclusion of case 696. -/
namespace N12Compact.C696NegativeCentral

open S12 S12Pilot S12Completion.C696 SideSignPacking
open C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have hi := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  have hj := ownerIndex_spec p (ownerMasks j) (by rw [hf]; exact ownerMasks_mem j)
  exact different (AuxiliaryNecessity.ownerMasks_injective
    (hi.symm.trans ((congrArg (markerCode p) equal).trans hj)))

private theorem inside (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (P : ℚ×ℚ)
    (member : P∈queryInsidePoints (ownerMasks i) 2 (auxiliaryVector i)) :
    (owners p i).Inside P.1 P.2 := C696WallCycle.inside_query p hf i P member

/-- A frame-equivalent negative central square forces actual ownership of
the center by original owner 6. Every geometric premise is supplied by the
original packing, its exact family, and the original missing-corner root. -/
theorem center_of_negative_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (corner : ¬(owners p 0).Inside 1 1)
    (A : OpenSquare) (T : ℝ) (hs : A.s=-T) (normal : Normal A.c T)
    (shape : A.side=(owners p 6).side)
    (equivalent : ∀ x y, A.Inside x y↔(owners p 6).Inside x y) :
    (owners p 6).Inside 2 2 := by
  have same : (owners p 0).side=A.side := by
    rw [shape]
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have side : 1<A.side := by rw [shape]; exact C696WallCycle.side_gt p 6
  have oM : (owners p 0).Inside 1 (457/500) := by
    simpa using inside p hf 0 ((1,457/500):ℚ×ℚ) (by decide +kernel)
  have oN : (owners p 0).Inside (28/25) 1 := by
    simpa using inside p hf 0 ((28/25,1):ℚ×ℚ) (by decide +kernel)
  have oF : (owners p 0).Inside (187/100) (19/25) := by
    simpa using inside p hf 0 ((187/100,19/25):ℚ×ℚ) (by decide +kernel)
  have missingM : ¬(owners p 0).Inside 2 (457/500) := by
    simpa using C696WallCycle.outside_query p hf 0 ((2,457/500):ℚ×ℚ)
      (by decide +kernel)
  have aP : A.Inside (33/20) (33/20) := (equivalent _ _).mpr (by
    simpa using inside p hf 6 ((33/20,33/20):ℚ×ℚ) (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (equivalent _ _).mpr (by
    simpa using inside p hf 6 ((2,87/50):ℚ×ℚ) (by decide +kernel))
  have aE : A.Inside (87/50) 2 := (equivalent _ _).mpr (by
    simpa using inside p hf 6 ((87/50,2):ℚ×ℚ) (by decide +kernel))
  have aNew : A.Inside (3/2) 2 :=
    (equivalent _ _).mpr (C696CentralReach.central_points p hf).2.2.2
  have lN : (owners p 1).Inside 1 (28/25) := by
    simpa using inside p hf 1 ((1,28/25):ℚ×ℚ) (by decide +kernel)
  have lW : (owners p 1).Inside 1 (87/50) := by
    simpa using inside p hf 1 ((1,87/50):ℚ×ℚ) (by decide +kernel)
  apply (equivalent 2 2).mp
  apply SouthwestNegativeCorner.point (owners p 0) A (owners p 1) T hs normal
    same side (p.contained _) oM oN oF corner missingM aP aD aE aNew lN lW
  · intro x y h
    exact apart p hf 0 6 (by decide) x y ⟨h.1,(equivalent x y).mp h.2⟩
  · intro x y h
    exact apart p hf 6 1 (by decide) x y ⟨(equivalent x y).mp h.1,h.2⟩

/-- The remaining actual packing sector is strictly positive, including
neither zero tilt nor any unexplained singleton orientation assumption. -/
theorem positive_frame_of_missing_center (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (corner : ¬(owners p 0).Inside 1 1)
    (center : ¬(owners p 6).Inside 2 2) :
    ∃ A : OpenSquare, 0<A.c ∧ 0<A.s ∧ A.s≤A.c ∧
      A.side=(owners p 6).side ∧
      (∀ x y, A.Inside x y↔(owners p 6).Inside x y) ∧ ¬A.Inside 2 2 := by
  obtain ⟨A,hc,canonical,shape,equivalent,_⟩ := ClosedFrames.canonical_frame (owners p 6)
  have positive : 0<A.s := by
    by_contra failure
    have nonpositive : A.s≤0 := le_of_not_gt failure
    have normal : Normal A.c (-A.s) := ⟨by linarith only [nonpositive],
      by simpa only [abs_of_nonpos nonpositive] using canonical,
      by nlinarith only [A.unit_normal]⟩
    exact center (center_of_negative_frame p hf corner A (-A.s) (by ring)
      normal shape equivalent)
  exact ⟨A,hc,positive,by simpa only [abs_of_pos positive] using canonical,
    shape,equivalent,fun h => center ((equivalent 2 2).mp h)⟩

#print axioms center_of_negative_frame

end N12Compact.C696NegativeCentral
