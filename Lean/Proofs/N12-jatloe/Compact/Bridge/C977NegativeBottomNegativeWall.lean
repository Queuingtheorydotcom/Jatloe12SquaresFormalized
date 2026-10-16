import Compact.Bridge.C977NegativeCentralFarFloor
import Compact.Bridge.C977NextBottomWall
import Compact.Geometry.NegativeBottomNegativeWallClosure

/-! The original nonpositive singleton / nonpositive bottom-wall cell
is empty. The shallow marker face uses the actual next-wall ending;
the steep face uses all four full O/D/B support selectors. No central
orientation restriction or reflected missing-corner premise is added. -/
namespace N12Compact.C977NegativeBottomNegativeWall

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (s r t : ℝ) (os : (q 0).s=-s) (on : Normal (q 0).c s)
    (ds : (q 9).s=-r) (dn : Normal (q 9).c r)
    (bs : (q 6).s=-t) (bn : Normal (q 6).c t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) : False := by
  have side (i : Fin 12) : 1<(q i).side := by
    rw [shape,p.congruent]
    exact p.side_gt_one
  have same (i j : Fin 12) : (q i).side=(q j).side := by
    rw [shape,shape,p.congruent,p.congruent]
  have box (i : Fin 12) : InsideContainer (q i) :=
    fun x y h => p.contained _ x y ((equivalent i x y).mp h)
  have apart (i j : Fin 12) (different : i≠j) :
      ∀ x y, ¬((q i).Inside x y ∧ (q j).Inside x y) := fun x y h =>
    p.disjoint _ _ (fun eq => different (ordered_owner_injective p hf eq)) x y
      ⟨(equivalent i _ _).mp h.1,(equivalent j _ _).mp h.2⟩
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
  have oMarker : (q 0).Inside 1 (457/500) := (equivalent 0 _ _).mpr (by
    have point := (om 0).mpr (by decide)
    simpa [Owns,marker] using point)
  have anchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have stronger := code_one_missing_points p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0) missingCorner
  have oNear := (equivalent 0 _ _).mpr anchors.near_point
  have oFar := (equivalent 0 _ _).mpr anchors.lower_point
  have oMissing : ¬(q 0).Inside 1 1 :=
    fun h => missingCorner ((equivalent 0 _ _).mp h)
  have oMissingMarker : ¬(q 0).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker)∉maskSupport (auxiliaryCode 0) := by decide
    exact absent ((om 13).mp (by simpa [Owns,marker] using (equivalent 0 _ _).mp h))
  have faces := corner_face (q 0) s os on (side 0) (box 0) oMarker oNear oFar oMissing
  have steep : 47/100<s ∧ 27/20<(q 0).c+s := by
    rcases NegativeBottomNextAxes.marker_escape (q 0) s os on (side 0) oMarker
        oMissingMarker faces.1 faces.2.2 with shallow | steep
    · exact False.elim (C977NextBottomWall.excludes_of_small_bottom p hf (q 0) s os on
        shallow.le (shape 0) (equivalent 0) missingCorner)
    · exact steep
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have dMarker : (q 9).Inside 2 (457/500) := (equivalent 9 _ _).mpr (by
    have point := (dm 13).mpr (by decide)
    simpa [Owns,marker] using point)
  have dHigh : (q 9).Inside (13/5) 1 :=
    (equivalent 9 _ _).mpr (C977BottomExtendedReach.point p hf missingCorner)
  have dFar := C977BottomNegativeExtendedReach.frame_point p hf (q 9) r ds dn
    (shape 9) (equivalent 9) missingCorner
  have dInner := C977NextBottomWall.negative_frame_point p hf (q 9) r ds dn
    (shape 9) (equivalent 9)
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have bWall : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have bOuter : (q 6).Inside 3 (8/5) :=
    (equivalent 6 _ _).mpr (C977OuterWings.points p hf).1
  have missingMiddle : ¬(q 6).Inside 3 2 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977WallMiddle.right_point p hf⟩
  have marked := (negative_bands (q 6) t _ _ bs).mp bMarker
  have wing := (negative_bands (q 6) t _ _ bs).mp bOuter
  have capV : (q 6).loV+(q 6).side≤2*(q 6).c+3*t := by
    apply le_of_not_gt
    intro high
    apply missingMiddle
    apply (negative_bands (q 6) t _ _ bs).mpr
    refine ⟨?_,?_,?_,by linarith only [high]⟩ <;>
      nlinarith only [marked.1,marked.2.2.1,wing.2.1,bn.1,bn.2.1,(canonical 6).1]
  have capU := (C977SignedCentralCorner.frame_cap p hf q shape equivalent canonical
    missingCorner center).2
  rw [bs] at capU
  have small := (C977NegativeCentralFarFloor.frame_bounds p hf q shape equivalent canonical
    r t ds dn bs bn missingCorner center).2
  exact NegativeBottomNegativeWallClosure.impossible (q 0) (q 9) (q 6) s r t os ds bs
    on dn bn (same 0 9) (same 9 6) (side 0) steep.1 small.le (box 0)
    oMarker oNear ((equivalent 0 _ _).mpr anchors.horizontal_point) oFar
    ((equivalent 0 _ _).mpr stronger.lower_point) oMissing dMarker dHigh dFar dInner
    bMarker bWall (by linarith only [capU]) capV
    (apart 0 9 (by decide)) (apart 9 6 (by decide))

#print axioms frame_excludes
end N12Compact.C977NegativeBottomNegativeWall
