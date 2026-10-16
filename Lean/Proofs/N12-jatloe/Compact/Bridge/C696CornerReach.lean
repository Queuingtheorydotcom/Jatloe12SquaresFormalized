import Compact.Bridge.C696CentralReach
import Compact.Geometry.SouthwestCornerTranspose

/-! The original C696 positive central frame, if it misses the center,
forces the actual left singleton to own its inner corner. This is the
transpose of the complete negative-central result on the full original
squares. No choice of a missing bottom corner or wall sign is needed.
Source only, uncompiled. -/
namespace N12Compact.C696CornerReach

open S12 S12Pilot S12Completion.C696 SideSignPacking C977CornerCubic
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

theorem left_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (A : OpenSquare) (an : Normal A.c A.s)
    (shape : A.side=(owners p 6).side)
    (equivalent : ∀ x y, A.Inside x y↔(owners p 6).Inside x y)
    (missingCenter : ¬(owners p 6).Inside 2 2) :
    (owners p 1).Inside 1 1 := by
  by_contra missing
  have same : (owners p 1).side=A.side := by
    rw [shape]
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have side : 1<A.side := by rw [shape]; exact C696WallCycle.side_gt p 6
  have lM : (owners p 1).Inside (457/500) 1 := by
    simpa using C696WallCycle.inside_query p hf 1 ((457/500,1):ℚ×ℚ)
      (by decide +kernel)
  have lN : (owners p 1).Inside 1 (28/25) := by
    simpa using C696WallCycle.inside_query p hf 1 ((1,28/25):ℚ×ℚ)
      (by decide +kernel)
  have lF : (owners p 1).Inside (19/25) (187/100) := by
    simpa using C696WallCycle.inside_query p hf 1 ((19/25,187/100):ℚ×ℚ)
      (by decide +kernel)
  have lMissing : ¬(owners p 1).Inside (457/500) 2 := by
    simpa using C696WallCycle.outside_query p hf 1 ((457/500,2):ℚ×ℚ)
      (by decide +kernel)
  have aP : A.Inside (33/20) (33/20) := (equivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((33/20,33/20):ℚ×ℚ)
      (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (equivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((2,87/50):ℚ×ℚ)
      (by decide +kernel))
  have aE : A.Inside (87/50) 2 := (equivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((87/50,2):ℚ×ℚ)
      (by decide +kernel))
  have aLow := (equivalent 2 (3/2)).mpr (C696CentralReach.central_points p hf).2.2.1
  have oN : (owners p 0).Inside (28/25) 1 := by
    simpa using C696WallCycle.inside_query p hf 0 ((28/25,1):ℚ×ℚ)
      (by decide +kernel)
  have oW : (owners p 0).Inside (87/50) 1 := by
    simpa using C696WallCycle.inside_query p hf 0 ((87/50,1):ℚ×ℚ)
      (by decide +kernel)
  have reach := SouthwestCornerTranspose.point (owners p 0) A (owners p 1)
    an same side (p.contained _) lM lN lF missing lMissing aP aD aE aLow oN oW
    (fun x y h => apart p hf 1 6 (by decide) x y
      ⟨h.1,(equivalent x y).mp h.2⟩)
    (fun x y h => apart p hf 6 0 (by decide) x y
      ⟨(equivalent x y).mp h.1,h.2⟩)
  exact missingCenter ((equivalent 2 2).mp reach)

#print axioms left_corner
end N12Compact.C696CornerReach
