import Compact.Bridge.C696CentralNormalForm
import Compact.Geometry.OwnedWestBottomAngle

/-! Complete original C696 exclusion. The normal form supplies one
actual southwest central/bottom pair, with the center missing and the
west point owned. The full O/A support argument forces a shallow bottom
angle, contradicting the actual bottom-wall/paired-corner chain already
retained by the normal form. No new local pose, support selector, frame
sign or auxiliary ownership premise is added. Source only, uncompiled. -/
namespace N12Compact.C696OwnedWestClosure

open S12 S12Pilot S12Completion.C696 SideSignPacking C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ∀ x y, ¬((owners p 0).Inside x y ∧ (owners p 6).Inside x y) := by
  apply p.disjoint
  intro equal
  have h0 := ownerIndex_spec p (ownerMasks 0) (by rw [hf]; exact ownerMasks_mem 0)
  have h6 := ownerIndex_spec p (ownerMasks 6) (by rw [hf]; exact ownerMasks_mem 6)
  have same := AuxiliaryNecessity.ownerMasks_injective
    (h0.symm.trans ((congrArg (markerCode p) equal).trans h6))
  norm_num at same

/-- Every normal-form input comes from the same original twelve-square
packing. This closes the owned-west residual without splitting L's sign. -/
theorem frame_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (A O : OpenSquare)
    (data : C696CentralNormalForm.Data p A O) : False := by
  let t : ℝ := -O.s
  have os : O.s=-t := by dsimp [t]; ring
  have on : Normal O.c t := ⟨by dsimp [t]; linarith only [data.bottomNegative],
    by simpa only [t,abs_of_neg data.bottomNegative] using data.bottomCanonical,
    by dsimp [t]; nlinarith only [O.unit_normal]⟩
  have sameOriginal : (owners p 0).side=(owners p 6).side := by
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have same := data.bottomSide.trans (sameOriginal.trans data.centralSide.symm)
  have side : 1<A.side := by
    rw [data.centralSide]
    exact C696WallCycle.side_gt p 6
  have box : InsideContainer O := fun x y h =>
    p.contained _ x y ((data.bottomInside x y).mp h)
  have oMarker : O.Inside 1 (457/500) := (data.bottomInside _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((1,457/500):ℚ×ℚ) (by decide +kernel))
  have oNear : O.Inside (28/25) 1 := (data.bottomInside _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((28/25,1):ℚ×ℚ) (by decide +kernel))
  have oFar : O.Inside (187/100) (19/25) := (data.bottomInside _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((187/100,19/25):ℚ×ℚ) (by decide +kernel))
  have oCorner : ¬O.Inside 1 1 := fun h => data.missingCorner ((data.bottomInside _ _).mp h)
  have oMissing : ¬O.Inside 2 (457/500) := by
    have h : ¬(owners p 0).Inside 2 (457/500) := by
      simpa using C696WallCycle.outside_query p hf 0 ((2,457/500):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((data.bottomInside _ _).mp own)
  have aMarker : A.Inside (33/20) (33/20) := (data.centralInside _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((33/20,33/20):ℚ×ℚ) (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (data.centralInside _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((2,87/50):ℚ×ℚ) (by decide +kernel))
  have aE : A.Inside (87/50) 2 := (data.centralInside _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((87/50,2):ℚ×ℚ) (by decide +kernel))
  have cross := C696CentralReach.central_points p hf
  have aLeft := (data.centralInside (3/2) 2).mpr cross.2.2.2
  have aLow := (data.centralInside 2 (3/2)).mpr cross.2.2.1
  have west := (data.centralInside 1 2).mpr data.centralWest
  have missingNW : ¬A.Inside (33/20) (47/20) := by
    have h : ¬(owners p 6).Inside (33/20) (47/20) := by
      simpa using C696WallCycle.outside_query p hf 6 ((33/20,47/20):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((data.centralInside _ _).mp own)
  have foreignLow : ¬A.Inside 1 (8/5) := by
    have h : ¬(owners p 6).Inside 1 (8/5) := by
      simpa using C696WallCycle.outside_query p hf 6 ((1,8/5):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((data.centralInside _ _).mp own)
  have cap : A.loU+A.side≤2*(A.c+A.s) := by
    have ab := normal_bounds data.centralNormal
    apply le_of_not_gt
    intro high
    apply data.missingCenter
    apply (data.centralInside 2 2).mp
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [aMarker.1,aD.2.2.1,aE.2.2.2,ab.1,data.centralNormal.1,high]
  have oa : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y) := fun x y h =>
    apart p hf x y ⟨(data.bottomInside _ _).mp h.1,(data.centralInside _ _).mp h.2⟩
  have small := OwnedWestBottomAngle.small_bottom O A t os on data.centralNormal
    same side box oMarker oNear oFar oCorner oMissing aMarker aD aLeft aLow
    west cap missingNW foreignLow oa
  dsimp [t] at small
  linarith only [small,data.bottomSteep]

/-- The unchanged whole-case contract, with all original orientations
and ownership alternatives covered by the actual normal-form transport. -/
theorem excludes : ExcludesCase 696 :=
  C696CentralNormalForm.excludes_of_normal_form frame_excludes

#print axioms frame_excludes
#print axioms excludes
end N12Compact.C696OwnedWestClosure
