import Compact.Bridge.C977PositiveCornerOrder
import Compact.Bridge.C977CornerReach
import Compact.Geometry.CornerWallMarkerCycle

/-! An original-family C977 exclusion for the positive-bottom,
negative-left-wall cell when the southwest central square owns (1,2)
and misses (2,2). Every marker, side, container and disjointness premise
of the continuous cycle is recovered from the actual packing. This is
one orientation/incidence sector, not an entire C977 exclusion.
Source only, uncompiled. -/
namespace N12Compact.C977OwnedWestCorner

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

private theorem forced_auxiliary (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (i : Fin 12) (n : Nat)
    (check : ∀ owned ∈ pruningDomain4 i, n∈owned) :
    n∈natCombinedOwners p (orderedOwner p i) :=
  check _ (pruned_auxiliary_domain_actual p hf i)

/-- The entire owned-west-point positive-bottom/negative-wall sector.
The individual face reindexings preserve the actual physical squares;
the left singleton's canonical frame is chosen internally. -/
theorem frame_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (on : Normal (q 0).c (q 0).s)
    (an : Normal (q 5).c (q 5).s) (wn : Normal (q 8).c t)
    (ws : (q 8).s=-t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2)
    (west : (p.square (orderedOwner p 5)).Inside 1 2) : False := by
  have side (i : Fin 12) : 1<(q i).side := by
    rw [shape,p.congruent]
    exact p.side_gt_one
  have same (i j : Fin 12) : (q i).side=(q j).side := by
    rw [shape,shape,p.congruent,p.congruent]
  have box (i : Fin 12) : InsideContainer (q i) :=
    fun x y h => p.contained _ x y ((equivalent i x y).mp h)
  have canonicalA : |(q 5).s|≤(q 5).c := by
    rw [abs_of_nonneg an.1]
    exact an.2.1
  have cornerOriginal : (p.square (orderedOwner p 1)).Inside 1 1 := by
    rcases C977CornerReach.frame_point_or_left_corner p hf missingCorner
        (q 5) canonicalA (shape 5) (equivalent 5) with center | remaining
    · exact False.elim (missingCenter center)
    · exact remaining.2
  obtain ⟨L,lc,canonicalL,lShape,lInside,_⟩ :=
    ClosedFrames.canonical_frame (p.square (orderedOwner p 1))
  have lSide : 1<L.side := by rw [lShape,p.congruent]; exact p.side_gt_one
  have sameOL : (q 0).side=L.side := by
    rw [shape,lShape,p.congruent,p.congruent]
  have sameLW : L.side=(q 8).side := by
    rw [lShape,shape,p.congruent,p.congruent]
  have lBox : InsideContainer L :=
    fun x y h => p.contained _ x y ((lInside x y).mp h)
  have oAnchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have lAnchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
  have lm := coded_exact p (orderedOwner p 1)
  rw [ordered_owner_code p hf 1] at lm
  have wm := coded_exact p (orderedOwner p 8)
  rw [ordered_owner_code p hf 8] at wm
  have oMarker : (q 0).Inside 1 (457/500) := (equivalent 0 _ _).mpr (by
    have h := (om 0).mpr (by decide)
    simpa [Owns,marker] using h)
  have oNear := (equivalent 0 _ _).mpr oAnchors.near_point
  have oFar := (equivalent 0 _ _).mpr oAnchors.lower_point
  have oMissing : ¬(q 0).Inside 1 1 :=
    fun h => missingCorner ((equivalent 0 _ _).mp h)
  have oNext : ¬(q 0).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker)∉maskSupport (auxiliaryCode 0) := by decide
    apply absent
    apply (om 13).mp
    simpa [Owns,marker] using (equivalent 0 _ _).mp h
  have lMarker : L.Inside (457/500) 1 := (lInside _ _).mpr (by
    have h := (lm 1).mpr (by decide)
    simpa [Owns,marker] using h)
  have corner : L.Inside 1 1 := (lInside _ _).mpr cornerOriginal
  have lFar : L.Inside (19/25) (187/100) := (lInside _ _).mpr lAnchors.2.2
  have wMarker : (q 8).Inside (457/500) 2 := (equivalent 8 _ _).mpr (by
    have h := (wm 12).mpr (by decide)
    simpa [Owns,marker] using h)
  have wHigh : (q 8).Inside 1 (12/5) := (equivalent 8 _ _).mpr (by
    have owned := forced_auxiliary p hf 8 11 (by decide)
    have point := (nat_combined_exact p (orderedOwner p 8) 11 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have wMissingTop : ¬(q 8).Inside (457/500) 3 := by
    intro h
    have absent : (7 : Marker)∉maskSupport (auxiliaryCode 8) := by decide
    apply absent
    apply (wm 7).mp
    simpa [Owns,marker] using (equivalent 8 _ _).mp h
  have wMissingNW : ¬(q 8).Inside (33/20) (47/20) := by
    intro h
    have absent : (11 : Marker)∉maskSupport (auxiliaryCode 8) := by decide
    apply absent
    apply (wm 11).mp
    simpa [Owns,marker] using (equivalent 8 _ _).mp h
  have wMissingFar : ¬(q 8).Inside (19/25) (187/100) := fun h =>
    apart p hf 8 1 (by decide) _ _ ⟨(equivalent 8 _ _).mp h,lAnchors.2.2⟩
  obtain ⟨marker0,d0,e0,_,_,_⟩ := C977CentralReach.central_data p hf
  have marker := (equivalent 5 _ _).mpr marker0
  have aD := (equivalent 5 _ _).mpr d0
  have aE := (equivalent 5 _ _).mpr e0
  have cross := C977CentralReach.central_points p hf
  have aLow := (equivalent 5 _ _).mpr cross.1
  have aLeft := (equivalent 5 _ _).mpr cross.2
  have ab := normal_bounds an
  have centerCap : (q 5).loU+(q 5).side≤2*((q 5).c+(q 5).s) := by
    apply le_of_not_gt
    intro high
    apply missingCenter
    apply (equivalent 5 2 2).mp
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [marker.1,ab.1,an.1]
    · linarith only [high]
    · linarith only [aD.2.2.1,ab.1]
    · linarith only [aE.2.2.2,an.1]
  have aw : ∀ x y, ¬((q 5).Inside x y ∧ (q 8).Inside x y) :=
    fun x y h => apart p hf 5 8 (by decide) x y
      ⟨(equivalent 5 x y).mp h.1,(equivalent 8 x y).mp h.2⟩
  have ol : ∀ x y, ¬((q 0).Inside x y ∧ L.Inside x y) :=
    fun x y h => apart p hf 0 1 (by decide) x y
      ⟨(equivalent 0 x y).mp h.1,(lInside x y).mp h.2⟩
  have lw : ∀ x y, ¬(L.Inside x y ∧ (q 8).Inside x y) :=
    fun x y h => apart p hf 1 8 (by decide) x y
      ⟨(lInside x y).mp h.1,(equivalent 8 x y).mp h.2⟩
  have lower := NegativeWallTopSeed.lower_face (q 5) (q 8) t an wn ws
    (same 5 8) (side 5) centerCap aLeft aLow marker wMarker wHigh wMissingFar aw
  have top := NegativeWallMarkerCap.upper_face (q 8) t wn ws (side 8)
    wMarker lower wMissingNW wMissingTop
  have northwest := NegativeWallMarkerCap.upper_u (q 8) t wn ws (side 8)
    wMarker lower wMissingNW
  have wallRange := NegativeWallMarkerCap.sector wn (side 8) rfl lower top
  have oFaces := C696PositiveCorner.corner_faces (q 0) on (side 0) (box 0)
    oMarker oNear oMissing oNext
  have bottomFace : CornerWallMarkerMixedBounds.boundary (q 0).c (q 0).s<
      (q 0).loV+(q 0).side := by
    simpa only [CornerWallMarkerMixedBounds.boundary,C696CornerMargins.boundary]
      using oFaces.2.2.2.2
  have order := C977PositiveCornerOrder.frame_angle_order_of_west p hf q shape
    equivalent t on an wn ws missingCorner missingCenter west
  apply CornerWallMarkerCycle.impossible (O := q 0) (L := L) (W := q 8) (t := t)
  exact {
    on := on, lc := lc, canonical := canonicalL, wn := wn, ws := ws,
    side := lSide, sameOL := sameOL, sameLW := sameLW,
    oBox := box 0, lBox := lBox, wBox := box 8,
    oMarker := oMarker, oNear := oNear, oFar := oFar,
    lMarker := lMarker, corner := corner, lFar := lFar, wMarker := wMarker,
    oCap := oFaces.2.2.1, bottomFace := bottomFace,
    northwest := northwest, top := top, order := order.le,
    small := wallRange.2.2.1.le, wide := wallRange.2.2.2.le,
    olApart := ol, lwApart := lw }

#print axioms frame_excludes
end N12Compact.C977OwnedWestCorner
