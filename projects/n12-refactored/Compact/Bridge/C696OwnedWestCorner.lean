import Compact.Bridge.C696CornerReach
import Compact.Geometry.PositiveCentralWallAngleOrder
import Compact.Geometry.CornerWallMarkerCycle
import Compact.Geometry.NegativeWallMarkerCap
import Compact.Geometry.NegativeWallTopSeed

/-! Original C696 positive-bottom / negative-wall exclusion with the
actual central west point owned. Every field of the complete signed-left
support cycle is supplied from original squares and query soundness.
The true marker caps replace the unavailable height2.88 point.
Source only, uncompiled. -/
namespace N12Compact.C696OwnedWestCorner

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

theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (O A W : OpenSquare) (t : ℝ)
    (on : Normal O.c O.s) (an : Normal A.c A.s) (wn : Normal W.c t) (ws : W.s=-t)
    (oShape : O.side=(owners p 0).side) (aShape : A.side=(owners p 6).side)
    (wShape : W.side=(owners p 8).side)
    (oEquivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (aEquivalent : ∀ x y, A.Inside x y↔(owners p 6).Inside x y)
    (wEquivalent : ∀ x y, W.Inside x y↔(owners p 8).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2)
    (west : (owners p 6).Inside 1 2) : False := by
  obtain ⟨L,lc,canonical,lShape,lEquivalent,_⟩ :=
    ClosedFrames.canonical_frame (owners p 1)
  have sameOriginal (i j : Fin 12) : (owners p i).side=(owners p j).side := by
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have sameOA : O.side=A.side := oShape.trans ((sameOriginal 0 6).trans aShape.symm)
  have sameAW : A.side=W.side := aShape.trans ((sameOriginal 6 8).trans wShape.symm)
  have sameOL : O.side=L.side := oShape.trans ((sameOriginal 0 1).trans lShape.symm)
  have sameLW : L.side=W.side := lShape.trans ((sameOriginal 1 8).trans wShape.symm)
  have side : 1<A.side := by rw [aShape]; exact C696WallCycle.side_gt p 6
  have sideCap : A.side≤1001/1000 := by rw [aShape]; exact C696WallCycle.side_le p 6
  have oSide : 1<O.side := by rwa [sameOA]
  have wSide : 1<W.side := by rwa [←sameAW]
  have lSide : 1<L.side := by rw [lShape]; exact C696WallCycle.side_gt p 1
  have oBox : InsideContainer O := fun x y h => p.contained _ x y ((oEquivalent x y).mp h)
  have lBox : InsideContainer L := fun x y h => p.contained _ x y ((lEquivalent x y).mp h)
  have wBox : InsideContainer W := fun x y h => p.contained _ x y ((wEquivalent x y).mp h)
  have oMarker : O.Inside 1 (457/500) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((1,457/500):ℚ×ℚ) (by decide +kernel))
  have oNear : O.Inside (28/25) 1 := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((28/25,1):ℚ×ℚ) (by decide +kernel))
  have oFar : O.Inside (187/100) (19/25) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((187/100,19/25):ℚ×ℚ) (by decide +kernel))
  have oMissing : ¬O.Inside 1 1 := fun h => missingCorner ((oEquivalent _ _).mp h)
  have oNext : ¬O.Inside 2 (457/500) := by
    have h : ¬(owners p 0).Inside 2 (457/500) := by
      simpa using C696WallCycle.outside_query p hf 0 ((2,457/500):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((oEquivalent _ _).mp own)
  have lMarker : L.Inside (457/500) 1 := (lEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 1 ((457/500,1):ℚ×ℚ) (by decide +kernel))
  have lFarOriginal : (owners p 1).Inside (19/25) (187/100) := by
    simpa using C696WallCycle.inside_query p hf 1 ((19/25,187/100):ℚ×ℚ) (by decide +kernel)
  have lFar := (lEquivalent _ _).mpr lFarOriginal
  have corner := (lEquivalent 1 1).mpr
    (C696CornerReach.left_corner p hf A an aShape aEquivalent missingCenter)
  have wMarker : W.Inside (457/500) 2 := (wEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 8 ((457/500,2):ℚ×ℚ) (by decide +kernel))
  have wPoint : W.Inside 1 (113/50) := (wEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 8 ((1,113/50):ℚ×ℚ) (by decide +kernel))
  have wHigh : W.Inside 1 (12/5) := (wEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 8 ((1,12/5):ℚ×ℚ) (by decide +kernel))
  have wMissingTop : ¬W.Inside (457/500) 3 := by
    have h : ¬(owners p 8).Inside (457/500) 3 := by
      simpa using C696WallCycle.outside_query p hf 8 ((457/500,3):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((wEquivalent _ _).mp own)
  have wMissingNW : ¬W.Inside (33/20) (47/20) := by
    have h : ¬(owners p 8).Inside (33/20) (47/20) := by
      simpa using C696WallCycle.outside_query p hf 8 ((33/20,47/20):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((wEquivalent _ _).mp own)
  have wMissingFar : ¬W.Inside (19/25) (187/100) := fun h =>
    apart p hf 8 1 (by decide) _ _ ⟨(wEquivalent _ _).mp h,lFarOriginal⟩
  have aMarker : A.Inside (33/20) (33/20) := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((33/20,33/20):ℚ×ℚ) (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((2,87/50):ℚ×ℚ) (by decide +kernel))
  have aE : A.Inside (87/50) 2 := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((87/50,2):ℚ×ℚ) (by decide +kernel))
  have cross := C696CentralReach.central_points p hf
  have aLeft := (aEquivalent (3/2) 2).mpr cross.2.2.2
  have aLow := (aEquivalent 2 (3/2)).mpr cross.2.2.1
  have aWest := (aEquivalent 1 2).mpr west
  have missingNW : ¬A.Inside (33/20) (47/20) := by
    have h : ¬(owners p 6).Inside (33/20) (47/20) := by
      simpa using C696WallCycle.outside_query p hf 6 ((33/20,47/20):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((aEquivalent _ _).mp own)
  have foreignLow : ¬A.Inside 1 (8/5) := by
    have h : ¬(owners p 6).Inside 1 (8/5) := by
      simpa using C696WallCycle.outside_query p hf 6 ((1,8/5):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((aEquivalent _ _).mp own)
  have ab := normal_bounds an
  have cap : A.loU+A.side≤2*(A.c+A.s) := by
    apply le_of_not_gt
    intro high
    apply missingCenter
    apply (aEquivalent 2 2).mp
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [aMarker.1,aD.2.2.1,aE.2.2.2,ab.1,an.1,high]
  have oa : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y) := fun x y h =>
    apart p hf 0 6 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(aEquivalent _ _).mp h.2⟩
  have aw : ∀ x y, ¬(A.Inside x y ∧ W.Inside x y) := fun x y h =>
    apart p hf 6 8 (by decide) x y ⟨(aEquivalent _ _).mp h.1,(wEquivalent _ _).mp h.2⟩
  have ol : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y) := fun x y h =>
    apart p hf 0 1 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(lEquivalent _ _).mp h.2⟩
  have lw : ∀ x y, ¬(L.Inside x y ∧ W.Inside x y) := fun x y h =>
    apart p hf 1 8 (by decide) x y ⟨(lEquivalent _ _).mp h.1,(wEquivalent _ _).mp h.2⟩
  have lower := NegativeWallTopSeed.lower_face A W t an wn ws sameAW side cap
    aLeft aLow aMarker wMarker wHigh wMissingFar aw
  have top := NegativeWallMarkerCap.upper_face W t wn ws wSide wMarker lower wMissingNW wMissingTop
  have northwest := NegativeWallMarkerCap.upper_u W t wn ws wSide wMarker lower wMissingNW
  have range := NegativeWallMarkerCap.sector wn wSide rfl lower top
  have oFaces := C696PositiveCorner.corner_faces O on oSide oBox oMarker oNear oMissing oNext
  have bottomFace : CornerWallMarkerMixedBounds.boundary O.c O.s<O.loV+O.side := by
    simpa only [CornerWallMarkerMixedBounds.boundary,C696CornerMargins.boundary]
      using oFaces.2.2.2.2
  have order := PositiveCentralWallAngleOrder.angle_order O A W t on an wn ws sameOA sameAW
    side sideCap oBox wBox oMarker oNear oFar oMissing oNext aMarker aD aLeft aLow aWest
    missingNW foreignLow cap wMarker wPoint wMissingTop wMissingFar oa aw
  apply CornerWallMarkerCycle.impossible (O := O) (L := L) (W := W) (t := t)
  exact {
    on := on, lc := lc, canonical := canonical, wn := wn, ws := ws,
    side := lSide, sameOL := sameOL, sameLW := sameLW,
    oBox := oBox, lBox := lBox, wBox := wBox,
    oMarker := oMarker, oNear := oNear, oFar := oFar,
    lMarker := lMarker, corner := corner, lFar := lFar, wMarker := wMarker,
    oCap := oFaces.2.2.1, bottomFace := bottomFace,
    northwest := northwest, top := top, order := order.le,
    small := range.2.2.1.le, wide := range.2.2.2.le,
    olApart := ol, lwApart := lw }

#print axioms frame_excludes
end N12Compact.C696OwnedWestCorner
