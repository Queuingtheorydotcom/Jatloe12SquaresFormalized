import Compact.Bridge.C696CornerReach
import Compact.Bridge.C696NegativeCentral
import Compact.Bridge.C696PositiveWallOwnedWest
import Compact.Bridge.C696OwnedWestCorner
import Compact.Geometry.PositiveCentralNegativeLeft
import Compact.Geometry.PositiveCentralPositiveLeftWest

/-! Positive bottom frames in the original C696 missing-corner root force
the central west point. Both signs of the actual left singleton are
discharged internally; the positive central frame and the left corner
are also derived from the original packing. No wall sign, added point,
saved pose interval, or whole-packing normalization is assumed.
Both signs of the actual wall are then excluded, leaving a strictly
negative bottom frame in this original missing-corner/center branch.
Source only, uncompiled. -/
namespace N12Compact.C696PositiveBottomWest

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

/-- Both left-frame signs are covered while the two supplied frames
describe exactly the original bottom and southwest central squares. -/
theorem frame_west (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (O A : OpenSquare) (on : Normal O.c O.s) (an : Normal A.c A.s)
    (oShape : O.side=(owners p 0).side) (aShape : A.side=(owners p 6).side)
    (oEquivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (aEquivalent : ∀ x y, A.Inside x y↔(owners p 6).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2) :
    (owners p 6).Inside 1 2 := by
  obtain ⟨L,lc,canonical,lShape,lEquivalent,_⟩ :=
    ClosedFrames.canonical_frame (owners p 1)
  have sameO : O.side=A.side := by
    rw [oShape,aShape]
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have sameL : L.side=A.side := by
    rw [lShape,aShape]
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have side : 1<A.side := by rw [aShape]; exact C696WallCycle.side_gt p 6
  have small : A.side≤1001/1000 := by rw [aShape]; exact C696WallCycle.side_le p 6
  have oBox : InsideContainer O := fun x y h =>
    p.contained _ x y ((oEquivalent x y).mp h)
  have lBox : InsideContainer L := fun x y h =>
    p.contained _ x y ((lEquivalent x y).mp h)
  have oMarker : O.Inside 1 (457/500) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((1,457/500):ℚ×ℚ) (by decide +kernel))
  have oNear : O.Inside (28/25) 1 := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((28/25,1):ℚ×ℚ) (by decide +kernel))
  have oFar : O.Inside (187/100) (19/25) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((187/100,19/25):ℚ×ℚ) (by decide +kernel))
  have oMissingCorner : ¬O.Inside 1 1 := fun h => missingCorner ((oEquivalent _ _).mp h)
  have oMissingMarker : ¬O.Inside 2 (457/500) := by
    have h : ¬(owners p 0).Inside 2 (457/500) := by
      simpa using C696WallCycle.outside_query p hf 0 ((2,457/500):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((oEquivalent _ _).mp own)
  have lCorner := (lEquivalent 1 1).mpr
    (C696CornerReach.left_corner p hf A an aShape aEquivalent missingCenter)
  have lNear : L.Inside 1 (28/25) := (lEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 1 ((1,28/25):ℚ×ℚ) (by decide +kernel))
  have lFar : L.Inside (19/25) (187/100) := (lEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 1 ((19/25,187/100):ℚ×ℚ) (by decide +kernel))
  have aMarker : A.Inside (33/20) (33/20) := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((33/20,33/20):ℚ×ℚ) (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((2,87/50):ℚ×ℚ) (by decide +kernel))
  have aE : A.Inside (87/50) 2 := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((87/50,2):ℚ×ℚ) (by decide +kernel))
  have cross := C696CentralReach.central_points p hf
  have aLeft := (aEquivalent (3/2) 2).mpr cross.2.2.2
  have aLow := (aEquivalent 2 (3/2)).mpr cross.2.2.1
  have aMissingNW : ¬A.Inside (33/20) (47/20) := by
    have h : ¬(owners p 6).Inside (33/20) (47/20) := by
      simpa using C696WallCycle.outside_query p hf 6 ((33/20,47/20):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((aEquivalent _ _).mp own)
  have aForeignLow : ¬A.Inside 1 (8/5) := by
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
  have oaApart : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y) := fun x y h =>
    apart p hf 0 6 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(aEquivalent _ _).mp h.2⟩
  have olApart : ∀ x y, ¬(O.Inside x y ∧ L.Inside x y) := fun x y h =>
    apart p hf 0 1 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(lEquivalent _ _).mp h.2⟩
  have laApart : ∀ x y, ¬(L.Inside x y ∧ A.Inside x y) := fun x y h =>
    apart p hf 1 6 (by decide) x y ⟨(lEquivalent _ _).mp h.1,(aEquivalent _ _).mp h.2⟩
  apply (aEquivalent 1 2).mp
  by_cases nonnegative : 0≤L.s
  · have ln : Normal L.c L.s :=
      ⟨nonnegative,(le_abs_self L.s).trans canonical,L.unit_normal⟩
    exact PositiveCentralPositiveLeftWest.west O L A on ln an sameO sameL side oBox lBox
      oMarker oNear oFar oMissingCorner oMissingMarker lCorner lNear lFar
      aMarker aD aE aLeft aLow cap aMissingNW aForeignLow oaApart olApart laApart
  · have negative : 0< -L.s := by linarith only [nonnegative]
    have ln : Normal L.c (-L.s) := ⟨negative.le,
      by simpa only [abs_of_neg (lt_of_not_ge nonnegative)] using canonical,
      by nlinarith only [L.unit_normal]⟩
    exact PositiveCentralNegativeLeft.west O L A (-L.s) on ln (by ring) negative an
      sameO sameL side small oBox lBox oMarker oNear oFar oMissingCorner oMissingMarker
      lCorner lNear lFar aMarker aD aE aLeft aLow cap aMissingNW aForeignLow
      oaApart olApart laApart

/-- The central frame is also derived internally: a nonpositive central
frame would already own the center. Only the actual bottom-frame sign
and the two original missing points remain in this entrance. -/
theorem west (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (O : OpenSquare) (on : Normal O.c O.s)
    (shape : O.side=(owners p 0).side)
    (equivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2) :
    (owners p 6).Inside 1 2 := by
  obtain ⟨A,_,positive,order,aShape,aEquivalent,_⟩ :=
    C696NegativeCentral.positive_frame_of_missing_center p hf missingCorner missingCenter
  exact frame_west p hf O A on ⟨positive.le,order,A.unit_normal⟩ shape aShape
    equivalent aEquivalent missingCorner missingCenter

/-- A complete original C696 positive-bottom / positive-wall cell.
The required central west point and both other frame signs are proved
internally from the actual packing. -/
theorem positive_wall_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (O W : OpenSquare)
    (on : Normal O.c O.s) (wn : Normal W.c W.s)
    (oShape : O.side=(owners p 0).side) (wShape : W.side=(owners p 8).side)
    (oEquivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (wEquivalent : ∀ x y, W.Inside x y↔(owners p 8).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2) : False := by
  have point := west p hf O on oShape oEquivalent missingCorner missingCenter
  exact C696PositiveWallOwnedWest.frame_excludes p hf 0 W wn
    (by simpa [C696WallCycle.wallOwner] using wShape)
    (by simpa [C696PositiveWallOwnedWest.frame,C696WallCycle.wallOwner] using wEquivalent)
    (by simpa [C696PositiveWallOwnedWest.frame,C696PositiveWallOwnedWest.centralOwner] using point)

/-- Complete original positive-bottom exclusion. Central, left-singleton
and left-wall frames are chosen internally and all their signs are
covered. Only the original missing corner and center remain explicit. -/
theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (O : OpenSquare) (on : Normal O.c O.s)
    (shape : O.side=(owners p 0).side)
    (equivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2) : False := by
  obtain ⟨A,_,positive,order,aShape,aEquivalent,_⟩ :=
    C696NegativeCentral.positive_frame_of_missing_center p hf missingCorner missingCenter
  have an : Normal A.c A.s := ⟨positive.le,order,A.unit_normal⟩
  have point := frame_west p hf O A on an shape aShape equivalent aEquivalent
    missingCorner missingCenter
  obtain ⟨W,_,canonical,wShape,wEquivalent,_⟩ :=
    ClosedFrames.canonical_frame (owners p 8)
  by_cases nonnegative : 0≤W.s
  · have wn : Normal W.c W.s :=
      ⟨nonnegative,(le_abs_self W.s).trans canonical,W.unit_normal⟩
    exact C696PositiveWallOwnedWest.frame_excludes p hf 0 W wn
      (by simpa [C696WallCycle.wallOwner] using wShape)
      (by simpa [C696PositiveWallOwnedWest.frame,C696WallCycle.wallOwner] using wEquivalent)
      (by simpa [C696PositiveWallOwnedWest.frame,C696PositiveWallOwnedWest.centralOwner] using point)
  · have negative : W.s<0 := lt_of_not_ge nonnegative
    have wn : Normal W.c (-W.s) := ⟨by linarith only [negative],
      by simpa only [abs_of_neg negative] using canonical,
      by nlinarith only [W.unit_normal]⟩
    exact C696OwnedWestCorner.frame_excludes p hf O A W (-W.s) on an wn (by ring)
      shape aShape wShape equivalent aEquivalent wEquivalent missingCorner missingCenter point

/-- Every canonical description of the actual bottom singleton has
strictly negative sine in the remaining original branch. -/
theorem canonical_sine_negative (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (O : OpenSquare)
    (canonical : |O.s|≤O.c) (shape : O.side=(owners p 0).side)
    (equivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2) : O.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  exact frame_excludes p hf O
    ⟨nonnegative,(le_abs_self O.s).trans canonical,O.unit_normal⟩
    shape equivalent missingCorner missingCenter

#print axioms frame_west
#print axioms west
#print axioms positive_wall_excludes
#print axioms frame_excludes
#print axioms canonical_sine_negative
end N12Compact.C696PositiveBottomWest
