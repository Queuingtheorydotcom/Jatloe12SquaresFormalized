import Compact.Bridge.C977PositiveBottomNegativeWall
import Compact.Geometry.PositiveBottomWallCentralAxis
import Compact.Geometry.CentralNegativePositiveBottom
import Compact.Geometry.PositiveBottomWallNeighborAxis
import Compact.Geometry.CentralNegativeSignedPositiveBottom
import Compact.Bridge.C977NegativeNeighbor

/-! The original positive bottom singleton and positive next wall retain
only the wall-owned upward separator. Its two incoming central axes are
then incompatible with either central orientation. Every point and
upper face is supplied by the original packing; no auxiliary assignment
or saved pose enclosure is added. Source only, awaiting Lean replay. -/
namespace N12Compact.C977PositiveBottomWallClosure

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

/-- This original separator reduction is independent of A's sign. -/
theorem frame_outgoing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (on : Normal (q 0).c (q 0).s) (dn : Normal (q 9).c (q 9).s)
    (t : ℝ) (bs : (q 6).s=-t) (bn : Normal (q 6).c t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) :
    (q 6).loV+(q 6).side≤2*(q 6).c+3*t ∧
      (q 9).loV+(q 9).side≤lower (q 6) (-(q 9).s) (q 9).c := by
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
  have oMissingMarker : ¬(q 0).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker)∉maskSupport (auxiliaryCode 0) := by decide
    exact absent ((om 13).mp (by simpa [Owns,marker] using (equivalent 0 _ _).mp h))
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have dMarker : (q 9).Inside 2 (457/500) := (equivalent 9 _ _).mpr (by
    have point := (dm 13).mpr (by decide)
    simpa [Owns,marker] using point)
  have dHigh : (q 9).Inside (13/5) 1 :=
    (equivalent 9 _ _).mpr (C977BottomExtendedReach.point p hf missingCorner)
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
  have faces := C696PositiveCorner.corner_faces (q 0) on (side 0) (box 0)
    oMarker ((equivalent 0 _ _).mpr anchors.near_point)
    (fun h => missingCorner ((equivalent 0 _ _).mp h)) oMissingMarker
  have incoming := PositiveBottomNextAxes.positive_wall (q 0) (q 9) on dn
    (same 0 9) (side 0) faces.2.1 oMarker
    ((equivalent 0 _ _).mpr anchors.near_point)
    ((equivalent 0 _ _).mpr anchors.lower_point) dMarker (apart 0 9 (by decide))
  have outgoing := CentralNegativeBottomAxes.alternatives (q 9) (q 6) t bs bn
    (canonical 9).1 (canonical 9).2 (same 9 6) (side 6) dMarker dHigh bMarker bWall
    (by linarith only [capU]) capV (apart 9 6 (by decide))
  refine ⟨capV,?_⟩
  rcases outgoing with central | wall
  · exact False.elim (PositiveBottomWallCentralAxis.impossible (q 0) (q 9) (q 6) t
      on dn bn (same 0 9) (same 9 6) (side 0) faces.2.1 faces.2.2.2.1
      (box 9) capV incoming central)
  · exact wall

/-- The actual wall-owned outgoing separator is incompatible with the
central incoming alternatives, independently of the bottom singleton. -/
theorem wall_axis_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (dn : Normal (q 9).c (q 9).s)
    (t : ℝ) (bs : (q 6).s=-t) (bn : Normal (q 6).c t)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (cap : (q 6).loV+(q 6).side≤2*(q 6).c+3*t)
    (outgoing : (q 9).loV+(q 9).side≤lower (q 6) (-(q 9).s) (q 9).c) : False := by
  have side (i : Fin 12) : 1<(q i).side := by
    rw [shape,p.congruent]
    exact p.side_gt_one
  have box : InsideContainer (q 9) :=
    fun x y h => p.contained _ x y ((equivalent 9 x y).mp h)
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have marker : (q 9).Inside 2 (457/500) := (equivalent 9 _ _).mpr (by
    have point := (dm 13).mpr (by decide)
    simpa [Owns,marker] using point)
  rcases (C977CenterIncoming.frame_cover p hf q shape equivalent canonical center).1 with
      own | neighboring | transverse
  · by_cases positive : 0≤(q 5).s
    · have an : Normal (q 5).c (q 5).s :=
        ⟨positive,by simpa only [abs_of_nonneg positive] using (canonical 5).2,
          (q 5).unit_normal⟩
      have owned := (equivalent 5 _ _).mpr center
      exact CentralNegativePositiveBottom.impossible (q 9) (q 6) t an bn dn bs
        (side 6) (side 9).le box marker cap
        (by linarith only [owned.2.1,own]) outgoing
    · have negative : (q 5).s<0 := lt_of_not_ge positive
      have an : Normal (q 5).c (-(q 5).s) :=
        ⟨by linarith only [negative],
          by simpa only [abs_of_neg negative] using (canonical 5).2,
          by nlinarith only [(q 5).unit_normal]⟩
      have low := (equivalent 5 _ _).mpr (C977CentralReach.central_points p hf).1
      apply CentralNegativeSignedPositiveBottom.impossible (q 9) (q 6) t an bn dn bs
        (by rw [shape,shape,p.congruent,p.congruent]) (side 9) box marker cap
      · simp only [neg_neg]
        linarith only [low.2.1,own]
      · exact outgoing
  · exact PositiveBottomWallNeighborAxis.impossible (q 5) (q 9) (q 6) t dn bn bs
      (by rw [shape,shape,p.congruent,p.congruent]) (side 9) box marker
      ((equivalent 5 _ _).mpr (C977CentralReach.central_points p hf).1)
      cap neighboring outgoing
  · nlinarith only [transverse.1,bs,bn.1,(canonical 6).1]

theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (on : Normal (q 0).c (q 0).s) (dn : Normal (q 9).c (q 9).s)
    (t : ℝ) (bs : (q 6).s=-t) (bn : Normal (q 6).c t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) : False := by
  have outgoing := frame_outgoing p hf q shape equivalent canonical on dn t bs bn
    missingCorner center
  exact wall_axis_excludes p hf q shape equivalent canonical dn t bs bn center
    outgoing.1 outgoing.2

/-- The actual next wall is forced positive before the preceding
all-angle central contradiction is applied. -/
theorem bottom_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (on : Normal (q 0).c (q 0).s)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) : False := by
  have cap := C977SignedCentralCorner.frame_cap p hf q shape equivalent canonical
    missingCorner center
  have bn : Normal (q 6).c (-(q 6).s) :=
    ⟨by linarith only [cap.1],
      by simpa only [abs_of_neg cap.1] using (canonical 6).2,
      by nlinarith only [(q 6).unit_normal]⟩
  have ds := C977PositiveBottomNegativeWall.wall_positive p hf q shape equivalent canonical
    on (-(q 6).s) (by ring) bn missingCorner center
  have dn : Normal (q 9).c (q 9).s :=
    ⟨ds.le,by simpa only [abs_of_pos ds] using (canonical 9).2,(q 9).unit_normal⟩
  exact frame_excludes p hf q shape equivalent canonical on dn (-(q 6).s)
    (by ring) bn missingCorner center

/-- No nonnegative canonical central frame remains in the original
missing-corner, center-owned branch. The two bottom signs are derived. -/
theorem positive_central_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (an : Normal (q 5).c (q 5).s)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2) : False := by
  have cap := C977SignedCentralCorner.frame_cap p hf q shape equivalent canonical
    missingCorner center
  have bn : Normal (q 6).c (-(q 6).s) :=
    ⟨by linarith only [cap.1],
      by simpa only [abs_of_neg cap.1] using (canonical 6).2,
      by nlinarith only [(q 6).unit_normal]⟩
  have os := C977NegativeNeighbor.bottom_positive p hf q shape equivalent canonical
    an (-(q 6).s) (by ring) bn missingCorner center
    (by simpa only [sub_neg_eq_add] using cap.2)
  have on : Normal (q 0).c (q 0).s :=
    ⟨os.le,by simpa only [abs_of_pos os] using (canonical 0).2,(q 0).unit_normal⟩
  exact bottom_excludes p hf q shape equivalent canonical on missingCorner center

#print axioms frame_outgoing
#print axioms wall_axis_excludes
#print axioms frame_excludes
#print axioms bottom_excludes
#print axioms positive_central_excludes
end N12Compact.C977PositiveBottomWallClosure
