import Compact.Bridge.C977OwnedWestCorner
import Compact.Bridge.C977PositiveWallOwnedWest
import Compact.Geometry.PositiveCentralNegativeLeft
import Compact.Geometry.PositiveCentralPositiveLeftWest

/-! Original C977 positive-bottom west-point entrance, with the actual
left singleton's sign selected internally. Every original point, missing
point, side and pairwise support premise is recovered from the packing.
Source only: no assembled Lean replay has yet been run. -/
namespace N12Compact.C977PositiveBottomWest

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

/-- The original positive-bottom / positive-central sector forces the
central west point for every orientation of the actual left singleton.
No wall-square sign, angle order, or owned-west premise is needed. -/
theorem frame_west (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (on : Normal (q 0).c (q 0).s) (an : Normal (q 5).c (q 5).s)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2) :
    (p.square (orderedOwner p 5)).Inside 1 2 := by
  have side : 1<(q 5).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have small : (q 5).side≤1001/1000 := by rw [shape,p.congruent]; exact p.side_le
  have sameOA : (q 0).side=(q 5).side := by
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
  have sameLA : L.side=(q 5).side := by
    rw [lShape,shape,p.congruent,p.congruent]
  have lBox : InsideContainer L :=
    fun x y h => p.contained _ x y ((lInside x y).mp h)
  have oaApart : ∀ x y, ¬((q 0).Inside x y ∧ (q 5).Inside x y) :=
    fun x y h => apart p hf 0 5 (by decide) x y
      ⟨(equivalent 0 x y).mp h.1,(equivalent 5 x y).mp h.2⟩
  have olApart : ∀ x y, ¬((q 0).Inside x y ∧ L.Inside x y) :=
    fun x y h => apart p hf 0 1 (by decide) x y
      ⟨(equivalent 0 x y).mp h.1,(lInside x y).mp h.2⟩
  have laApart : ∀ x y, ¬(L.Inside x y ∧ (q 5).Inside x y) :=
    fun x y h => apart p hf 1 5 (by decide) x y
      ⟨(lInside x y).mp h.1,(equivalent 5 x y).mp h.2⟩
  have oAnchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have lAnchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
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
  have lCorner := (lInside _ _).mpr cornerOriginal
  have lNear := (lInside _ _).mpr lAnchors.1
  have lFar := (lInside _ _).mpr lAnchors.2.2
  obtain ⟨marker0,d0,e0,_,northwest0,_⟩ := C977CentralReach.central_data p hf
  have marker := (equivalent 5 _ _).mpr marker0
  have aD := (equivalent 5 _ _).mpr d0
  have aE := (equivalent 5 _ _).mpr e0
  have cross := C977CentralReach.central_points p hf
  have aLow := (equivalent 5 _ _).mpr cross.1
  have aLeft := (equivalent 5 _ _).mpr cross.2
  have missingNW : ¬(q 5).Inside (33/20) (47/20) :=
    fun h => northwest0 ((equivalent 5 _ _).mp h)
  have lowOriginal : (p.square (orderedOwner p 1)).Inside 1 (8/5) := by
    have check : ∀ owned ∈ pruningDomain4 1, 10∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 1)
    have point := (nat_combined_exact p (orderedOwner p 1) 10 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have foreignLow : ¬(q 5).Inside 1 (8/5) := fun h =>
    apart p hf 5 1 (by decide) _ _ ⟨(equivalent 5 _ _).mp h,lowOriginal⟩
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
  apply (equivalent 5 1 2).mp
  by_cases sign : 0≤L.s
  · have ln : Normal L.c L.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalL,L.unit_normal⟩
    exact PositiveCentralPositiveLeftWest.west (q 0) L (q 5) on ln an
      sameOA sameLA side (box 0) lBox oMarker oNear oFar oMissing oNext
      lCorner lNear lFar marker aD aE aLeft aLow centerCap missingNW foreignLow
      oaApart olApart laApart
  · have negative : L.s<0 := lt_of_not_ge sign
    have ln : Normal L.c (-L.s) :=
      ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonicalL,
        by nlinarith only [L.unit_normal]⟩
    exact PositiveCentralNegativeLeft.west (q 0) L (q 5) (-L.s) on ln
      (by ring) (by linarith only [negative]) an sameOA sameLA side small
      (box 0) lBox oMarker oNear oFar oMissing oNext
      lCorner lNear lFar marker aD aE aLeft aLow centerCap missingNW foreignLow
      oaApart olApart laApart

/-- The entire original positive-bottom / positive-central /
negative-wall sector, with the left singleton sign and west point
handled internally. This is an orientation sector, not the whole family. -/
theorem frame_negative_wall_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (on : Normal (q 0).c (q 0).s) (an : Normal (q 5).c (q 5).s)
    (wn : Normal (q 8).c t) (ws : (q 8).s=-t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2) : False := by
  have west := frame_west p hf q shape equivalent on an missingCorner missingCenter
  exact C977OwnedWestCorner.frame_excludes p hf q shape equivalent t on an wn ws
    missingCorner missingCenter west

/-- The whole original positive-bottom / positive-central missing-center
sector. Both the left singleton and wall frames are chosen internally;
neither sign nor an assumed west point remains at this interface. -/
theorem frame_excludes (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (on : Normal (q 0).c (q 0).s) (an : Normal (q 5).c (q 5).s)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2) : False := by
  have west := frame_west p hf q shape equivalent on an missingCorner missingCenter
  obtain ⟨W,wc,canonicalW,wShape,wInside,_⟩ :=
    ClosedFrames.canonical_frame (p.square (orderedOwner p 8))
  by_cases sign : 0≤W.s
  · have wn : Normal W.c W.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalW,W.unit_normal⟩
    exact C977PositiveWallOwnedWest.frame_excludes p hf W wn wShape wInside west
  · have negative : W.s<0 := lt_of_not_ge sign
    have wn : Normal W.c (-W.s) :=
      ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonicalW,
        by nlinarith only [W.unit_normal]⟩
    let q' : Fin 12 → OpenSquare := fun i => if i=8 then W else q i
    have shape' (i : Fin 12) : (q' i).side=(p.square (orderedOwner p i)).side := by
      by_cases same : i=8
      · subst i
        simpa only [q',if_pos rfl] using wShape
      · simpa only [q',if_neg same] using shape i
    have equivalent' (i : Fin 12) (x y : ℝ) :
        (q' i).Inside x y↔(p.square (orderedOwner p i)).Inside x y := by
      by_cases same : i=8
      · subst i
        simpa only [q',if_pos rfl] using wInside x y
      · simpa only [q',if_neg same] using equivalent i x y
    have on' : Normal (q' 0).c (q' 0).s := by
      simpa only [q',if_neg (show (0 : Fin 12)≠8 by decide)] using on
    have an' : Normal (q' 5).c (q' 5).s := by
      simpa only [q',if_neg (show (5 : Fin 12)≠8 by decide)] using an
    have wn' : Normal (q' 8).c (-W.s) := by
      simpa only [q',if_pos rfl] using wn
    have ws : (q' 8).s=-(-W.s) := by
      simp only [q',if_pos rfl,neg_neg]
    exact C977OwnedWestCorner.frame_excludes p hf q' shape' equivalent' (-W.s)
      on' an' wn' ws missingCorner missingCenter west

/-- The same complete sector expressed as the two actual remaining
point alternatives, for use by the original family assembly. -/
theorem frame_point_or_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (on : Normal (q 0).c (q 0).s) (an : Normal (q 5).c (q 5).s) :
    (p.square (orderedOwner p 0)).Inside 1 1 ∨
      (p.square (orderedOwner p 5)).Inside 2 2 := by
  by_cases corner : (p.square (orderedOwner p 0)).Inside 1 1
  · exact Or.inl corner
  · right
    by_contra center
    exact frame_excludes p hf q shape equivalent on an corner center

/-- Exact remaining original entrance under the two missing points.
The central sign and left-corner incidence were already forced by the
corner reach theorem; the completed positive-bottom sector now also
forces the bottom frame to be strictly negative. -/
theorem frame_residual (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12 → OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonicalO : |(q 0).s|≤(q 0).c) (canonicalA : |(q 5).s|≤(q 5).c)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (missingCenter : ¬(p.square (orderedOwner p 5)).Inside 2 2) :
    (q 0).s<0 ∧ 0<(q 5).s ∧ (p.square (orderedOwner p 1)).Inside 1 1 := by
  have remaining : 0<(q 5).s ∧ (p.square (orderedOwner p 1)).Inside 1 1 := by
    rcases C977CornerReach.frame_point_or_left_corner p hf missingCorner
        (q 5) canonicalA (shape 5) (equivalent 5) with center | other
    · exact False.elim (missingCenter center)
    · exact other
  have an : Normal (q 5).c (q 5).s :=
    ⟨remaining.1.le,by simpa only [abs_of_pos remaining.1] using canonicalA,
      (q 5).unit_normal⟩
  refine ⟨?_,remaining⟩
  by_contra nonnegative
  have sign : 0≤(q 0).s := le_of_not_gt nonnegative
  have on : Normal (q 0).c (q 0).s :=
    ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalO,(q 0).unit_normal⟩
  exact frame_excludes p hf q shape equivalent on an missingCorner missingCenter

#print axioms frame_west
#print axioms frame_negative_wall_excludes
#print axioms frame_excludes
#print axioms frame_point_or_corner
#print axioms frame_residual
end N12Compact.C977PositiveBottomWest
