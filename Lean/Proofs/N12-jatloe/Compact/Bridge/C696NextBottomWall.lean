import Compact.Bridge.C696PositiveBottomWest
import Compact.Geometry.PositiveWallPositiveLeft
import Compact.Geometry.NegativeBottomNextWall
import Compact.Geometry.NegativeBottomInnerWall
import Compact.Bridge.C696PositiveWallOwnedWest

/-! The actual omitted bottom wall inherits the negative orientation in
the original C696 missing-corner, missing-center, missing-west branch.
The bottom singleton sign and its small angle are both proved internally
from the original packing. The paired southeast corner then forces the
negative next wall to own (2,1), closing every remaining O/D axis. This
excludes the entire missing-west branch, not yet the whole C696 case.
Source only, uncompiled. -/
namespace N12Compact.C696NextBottomWall

open S12 S12Pilot S12Completion.C696 SideSignPacking C977CornerCubic
set_option Elab.async false

private noncomputable def transpose (q : OpenSquare) : OpenSquare where
  c := q.c
  s := -q.s
  loU := q.loV
  loV := q.loU
  side := q.side
  unit_normal := by nlinarith only [q.unit_normal]
  side_pos := q.side_pos

private theorem inside_transpose (q : OpenSquare) (x y : ℝ) :
    (transpose q).Inside x y↔q.Inside y x := by
  dsimp [transpose,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((owners p i).Inside x y ∧ (owners p j).Inside x y) := by
  apply p.disjoint
  intro equal
  have hi := ownerIndex_spec p (ownerMasks i) (by rw [hf]; exact ownerMasks_mem i)
  have hj := ownerIndex_spec p (ownerMasks j) (by rw [hf]; exact ownerMasks_mem j)
  exact different (AuxiliaryNecessity.ownerMasks_injective
    (hi.symm.trans ((congrArg (markerCode p) equal).trans hj)))

/-- The entire actual bottom-wall and paired-corner chain excludes a
shallow negative bottom singleton. All central hypotheses have been
removed from this interface. -/
theorem excludes_of_small_bottom (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (O : OpenSquare) (t : ℝ)
    (os : O.s=-t) (on : Normal O.c t) (small : t≤1/5)
    (oShape : O.side=(owners p 0).side)
    (oEquivalent : ∀ x y, O.Inside x y↔(owners p 0).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1) : False := by
  obtain ⟨D,_,canonical,dShape,dEquivalent,_⟩ := ClosedFrames.canonical_frame (owners p 9)
  have sameOriginal : (owners p 0).side=(owners p 9).side := by
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have sameOD := oShape.trans (sameOriginal.trans dShape.symm)
  have side : 1<O.side := by rw [oShape]; exact C696WallCycle.side_gt p 0
  have oBox : InsideContainer O := fun x y h => p.contained _ x y ((oEquivalent x y).mp h)
  have dBox : InsideContainer D := fun x y h => p.contained _ x y ((dEquivalent x y).mp h)
  have oMarker : O.Inside 1 (457/500) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((1,457/500):ℚ×ℚ) (by decide +kernel))
  have oNear : O.Inside (28/25) 1 := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((28/25,1):ℚ×ℚ) (by decide +kernel))
  have oMiddle : O.Inside (87/50) 1 := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((87/50,1):ℚ×ℚ) (by decide +kernel))
  have oFar : O.Inside (187/100) (19/25) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((187/100,19/25):ℚ×ℚ) (by decide +kernel))
  have oCorner : ¬O.Inside 1 1 := fun h => missingCorner ((oEquivalent _ _).mp h)
  have dMarker : D.Inside 2 (457/500) := (dEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 9 ((2,457/500):ℚ×ℚ) (by decide +kernel))
  have dMissing : ¬D.Inside 3 (457/500) := by
    have h : ¬(owners p 9).Inside 3 (457/500) := by
      simpa using C696WallCycle.outside_query p hf 9 ((3,457/500):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((dEquivalent _ _).mp own)
  have od : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y) := fun x y h =>
    apart p hf 0 9 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(dEquivalent _ _).mp h.2⟩
  by_cases nonnegative : 0≤D.s
  · have dn : Normal D.c D.s :=
      ⟨nonnegative,(le_abs_self D.s).trans canonical,D.unit_normal⟩
    exact NegativeBottomNextWall.impossible O D t os on dn small sameOD side
      oBox dBox oMarker oNear oMiddle oFar oCorner dMarker dMissing od
  · have negativeD : D.s<0 := lt_of_not_ge nonnegative
    let r : ℝ := -D.s
    have ds : D.s=-r := by dsimp [r]; ring
    have dn : Normal D.c r := ⟨by dsimp [r]; linarith only [negativeD],
      by simpa only [r,abs_of_neg negativeD] using canonical,
      by dsimp [r]; nlinarith only [D.unit_normal]⟩
    have swappedNormal : Normal (transpose D).c (transpose D).s := by
      simpa only [transpose,r] using dn
    have swappedShape : (transpose D).side=
        (owners p (C696WallCycle.wallOwner 1)).side := by
      change D.side=(owners p 9).side
      exact dShape
    have swappedEquivalent : ∀ x y, (transpose D).Inside x y↔
        (C696PositiveWallOwnedWest.frame
          (owners p (C696WallCycle.wallOwner 1)) 1).Inside x y := by
      intro x y
      change (transpose D).Inside x y↔(pullSwap (owners p 9)).Inside x y
      rw [inside_transpose,inside_pullSwap]
      exact dEquivalent y x
    have swappedPoint := C696PositiveWallOwnedWest.frame_point p hf 1
      (transpose D) swappedNormal swappedShape swappedEquivalent
    have inner : D.Inside 2 1 := (inside_transpose D 1 2).mp swappedPoint
    exact NegativeBottomInnerWall.impossible O D t r os ds on dn small sameOD side
      oBox oMarker oNear oMiddle oFar oCorner dMarker inner od

/-- Both signs of the actual next bottom wall are excluded. The negative
sign uses its inner point forced by the actual southeast paired corner. -/
theorem frame_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (D : OpenSquare)
    (canonical : |D.s|≤D.c) (dShape : D.side=(owners p 9).side)
    (dEquivalent : ∀ x y, D.Inside x y↔(owners p 9).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2)
    (missingWest : ¬(owners p 6).Inside 1 2) : False := by
  obtain ⟨O,_,oCanonical,oShape,oEquivalent,_⟩ :=
    ClosedFrames.canonical_frame (owners p 0)
  have negative := C696PositiveBottomWest.canonical_sine_negative p hf O
    oCanonical oShape oEquivalent missingCorner missingCenter
  let t : ℝ := -O.s
  have os : O.s=-t := by dsimp [t]; ring
  have on : Normal O.c t := ⟨by dsimp [t]; linarith only [negative],
    by simpa only [t,abs_of_neg negative] using oCanonical,
    by dsimp [t]; nlinarith only [O.unit_normal]⟩
  obtain ⟨A,_,positive,order,aShape,aEquivalent,_⟩ :=
    C696NegativeCentral.positive_frame_of_missing_center p hf missingCorner missingCenter
  have an : Normal A.c A.s := ⟨positive.le,order,A.unit_normal⟩
  have sameOriginal (i j : Fin 12) : (owners p i).side=(owners p j).side := by
    change (p.square _).side=(p.square _).side
    rw [p.congruent,p.congruent]
  have sameOA : O.side=A.side := oShape.trans ((sameOriginal 0 6).trans aShape.symm)
  have sameOD : O.side=D.side := oShape.trans ((sameOriginal 0 9).trans dShape.symm)
  have side : 1<A.side := by rw [aShape]; exact C696WallCycle.side_gt p 6
  have oBox : InsideContainer O := fun x y h => p.contained _ x y ((oEquivalent x y).mp h)
  have dBox : InsideContainer D := fun x y h => p.contained _ x y ((dEquivalent x y).mp h)
  have oMarker : O.Inside 1 (457/500) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((1,457/500):ℚ×ℚ) (by decide +kernel))
  have oNear : O.Inside (28/25) 1 := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((28/25,1):ℚ×ℚ) (by decide +kernel))
  have oMiddle : O.Inside (87/50) 1 := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((87/50,1):ℚ×ℚ) (by decide +kernel))
  have oFar : O.Inside (187/100) (19/25) := (oEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 0 ((187/100,19/25):ℚ×ℚ) (by decide +kernel))
  have oCorner : ¬O.Inside 1 1 := fun h => missingCorner ((oEquivalent _ _).mp h)
  have oMissing : ¬O.Inside 2 (457/500) := by
    have h : ¬(owners p 0).Inside 2 (457/500) := by
      simpa using C696WallCycle.outside_query p hf 0 ((2,457/500):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((oEquivalent _ _).mp own)
  have aMarker : A.Inside (33/20) (33/20) := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((33/20,33/20):ℚ×ℚ) (by decide +kernel))
  have aD : A.Inside 2 (87/50) := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((2,87/50):ℚ×ℚ) (by decide +kernel))
  have aE : A.Inside (87/50) 2 := (aEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 6 ((87/50,2):ℚ×ℚ) (by decide +kernel))
  have cross := C696CentralReach.central_points p hf
  have aLeft := (aEquivalent (3/2) 2).mpr cross.2.2.2
  have aLow := (aEquivalent 2 (3/2)).mpr cross.2.2.1
  have aMissing : ¬A.Inside 1 2 := fun h => missingWest ((aEquivalent _ _).mp h)
  have aMissingNW : ¬A.Inside (33/20) (47/20) := by
    have h : ¬(owners p 6).Inside (33/20) (47/20) := by
      simpa using C696WallCycle.outside_query p hf 6 ((33/20,47/20):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((aEquivalent _ _).mp own)
  have aForeignLow : ¬A.Inside 1 (8/5) := by
    have h : ¬(owners p 6).Inside 1 (8/5) := by
      simpa using C696WallCycle.outside_query p hf 6 ((1,8/5):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((aEquivalent _ _).mp own)
  have cap : A.loU+A.side≤2*(A.c+A.s) := by
    have ab := normal_bounds an
    apply le_of_not_gt
    intro high
    apply missingCenter
    apply (aEquivalent 2 2).mp
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [aMarker.1,aD.2.2.1,aE.2.2.2,ab.1,an.1,high]
  have oa : ∀ x y, ¬(O.Inside x y ∧ A.Inside x y) := fun x y h =>
    apart p hf 0 6 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(aEquivalent _ _).mp h.2⟩
  have cuts := PositiveWallPositiveLeft.cuts O A t os on an sameOA side oBox
    oMarker oNear oFar oCorner oMissing aMarker aD aLeft aLow cap aMissing
    aMissingNW aForeignLow oa
  have dMarker : D.Inside 2 (457/500) := (dEquivalent _ _).mpr (by
    simpa using C696WallCycle.inside_query p hf 9 ((2,457/500):ℚ×ℚ) (by decide +kernel))
  have dMissing : ¬D.Inside 3 (457/500) := by
    have h : ¬(owners p 9).Inside 3 (457/500) := by
      simpa using C696WallCycle.outside_query p hf 9 ((3,457/500):ℚ×ℚ) (by decide +kernel)
    exact fun own => h ((dEquivalent _ _).mp own)
  have od : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y) := fun x y h =>
    apart p hf 0 9 (by decide) x y ⟨(oEquivalent _ _).mp h.1,(dEquivalent _ _).mp h.2⟩
  by_cases nonnegative : 0≤D.s
  · have dn : Normal D.c D.s :=
      ⟨nonnegative,(le_abs_self D.s).trans canonical,D.unit_normal⟩
    exact NegativeBottomNextWall.impossible O D t os on dn cuts.small.le sameOD
      (by rwa [sameOA]) oBox dBox oMarker oNear oMiddle oFar oCorner dMarker dMissing od
  · have negativeD : D.s<0 := lt_of_not_ge nonnegative
    let r : ℝ := -D.s
    have ds : D.s=-r := by dsimp [r]; ring
    have dn : Normal D.c r := ⟨by dsimp [r]; linarith only [negativeD],
      by simpa only [r,abs_of_neg negativeD] using canonical,
      by dsimp [r]; nlinarith only [D.unit_normal]⟩
    have swappedNormal : Normal (transpose D).c (transpose D).s := by
      simpa only [transpose,r] using dn
    have swappedShape : (transpose D).side=
        (owners p (C696WallCycle.wallOwner 1)).side := by
      change D.side=(owners p 9).side
      exact dShape
    have swappedEquivalent : ∀ x y, (transpose D).Inside x y↔
        (C696PositiveWallOwnedWest.frame
          (owners p (C696WallCycle.wallOwner 1)) 1).Inside x y := by
      intro x y
      change (transpose D).Inside x y↔(pullSwap (owners p 9)).Inside x y
      rw [inside_transpose,inside_pullSwap]
      exact dEquivalent y x
    have swappedPoint := C696PositiveWallOwnedWest.frame_point p hf 1
      (transpose D) swappedNormal swappedShape swappedEquivalent
    have inner : D.Inside 2 1 := (inside_transpose D 1 2).mp swappedPoint
    exact NegativeBottomInnerWall.impossible O D t r os ds on dn cuts.small.le
      sameOD (by rwa [sameOA]) oBox oMarker oNear oMiddle oFar oCorner dMarker inner od

/-- The entire original missing-west branch is impossible. No frame,
sign, support choice, or quantitative angle premise remains unbound. -/
theorem missing_west (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2)
    (missingWest : ¬(owners p 6).Inside 1 2) : False := by
  obtain ⟨D,_,canonical,shape,equivalent,_⟩ :=
    ClosedFrames.canonical_frame (owners p 9)
  exact frame_excludes p hf D canonical shape equivalent missingCorner missingCenter missingWest

/-- Preserved orientation interface, now a consequence of exclusion of
the entire original branch. -/
theorem canonical_sine_negative (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (D : OpenSquare)
    (canonical : |D.s|≤D.c) (dShape : D.side=(owners p 9).side)
    (dEquivalent : ∀ x y, D.Inside x y↔(owners p 9).Inside x y)
    (missingCorner : ¬(owners p 0).Inside 1 1)
    (missingCenter : ¬(owners p 6).Inside 2 2)
    (missingWest : ¬(owners p 6).Inside 1 2) : D.s<0 :=
  False.elim (frame_excludes p hf D canonical dShape dEquivalent
    missingCorner missingCenter missingWest)

#print axioms frame_excludes
#print axioms excludes_of_small_bottom
#print axioms missing_west
#print axioms canonical_sine_negative
end N12Compact.C696NextBottomWall
