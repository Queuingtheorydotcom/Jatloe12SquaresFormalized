import Compact.Bridge.C977CenterIncoming
import Compact.Bridge.C977WallMiddle
import Compact.Bridge.C977NextBottomWall
import Compact.Geometry.CentralNegativeNeighbor
import Compact.Geometry.CentralSteeperNegativeBottom

/-! The remaining negative southeast-central cap in the original family.
Both incoming axes sharpen the actual center square. This also closes
every nonpositive bottom-singleton frame in the missing-corner root; the
positive bottom continuation is retained explicitly. -/
namespace N12Compact.C977NegativeNeighbor

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem frame_sharpen (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (an : Normal (q 5).c (q 5).s) (t : ℝ)
    (signed : (q 6).s=-t) (bn : Normal (q 6).c t)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (capU : (q 6).loU+(q 6).side≤3*(q 6).c-t) :
    (q 5).s<2/5 ∧ (q 5).loU+(q 5).side≤2*((q 5).c+(q 5).s)+(9/100)*(q 5).c := by
  have side (i : Fin 12) : 1<(q i).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have same : (q 5).side=(q 6).side := by rw [shape,shape,p.congruent,p.congruent]
  have markerData := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at markerData
  have marker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (markerData 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have outer : (q 6).Inside 3 (8/5) :=
    (equivalent 6 _ _).mpr (C977OuterWings.points p hf).1
  have missing : ¬(q 6).Inside 3 2 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977WallMiddle.right_point p hf⟩
  have m := (negative_bands (q 6) t _ _ signed).mp marker
  have w := (negative_bands (q 6) t _ _ signed).mp outer
  have capV : (q 6).loV+(q 6).side≤2*(q 6).c+3*t := by
    apply le_of_not_gt
    intro high
    apply missing
    apply (negative_bands (q 6) t _ _ signed).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [m.1,m.2.2.1,w.2.1,bn.1,bn.2.1,(canonical 6).1,high]
  have caps := C977CenterCaps.frame_caps p hf (q 5) (canonical 5).1 (canonical 5).2
    (shape 5) (equivalent 5) center
  rcases C977CenterIncoming.positive_right_alternatives p hf q shape equivalent canonical
      an center with own | neighboring
  · exact CentralNegativeNeighbor.own_axis (q 5) (q 6) t signed an bn (side 6)
      ((equivalent 5 _ _).mpr center) capU capV own
  · rw [signed] at neighboring
    exact CentralNegativeNeighbor.neighbor_axis (q 5) (q 6) t signed an bn same (side 5)
      ((equivalent 5 _ _).mpr center) caps.2 capU neighboring

theorem negative_bottom_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (an : Normal (q 5).c (q 5).s) (t r : ℝ)
    (signed : (q 6).s=-t) (bn : Normal (q 6).c t)
    (os : (q 0).s=-r) (on : Normal (q 0).c r)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (capU : (q 6).loU+(q 6).side≤3*(q 6).c-t) : False := by
  have sharpen := frame_sharpen p hf q shape equivalent canonical an t signed bn center capU
  have caps := C977CenterCaps.frame_caps p hf (q 5) (canonical 5).1 (canonical 5).2
    (shape 5) (equivalent 5) center
  have anchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have om := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at om
  have oMarker : (q 0).Inside 1 (457/500) := (equivalent 0 _ _).mpr (by
    have point := (om 0).mpr (by decide)
    simpa [Owns,marker] using point)
  have oMissing : ¬(q 0).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker)∉maskSupport (auxiliaryCode 0) := by decide
    exact absent ((om 13).mp (by simpa [Owns,marker] using (equivalent 0 _ _).mp h))
  have data := C977CentralReach.central_data p hf
  have apart : ∀ x y, ¬((q 0).Inside x y ∧ (q 5).Inside x y) := fun x y h =>
    p.disjoint _ _ (fun eq => (by decide : (0 : Fin 12)≠5)
      (ordered_owner_injective p hf eq)) x y
      ⟨(equivalent 0 _ _).mp h.1,(equivalent 5 _ _).mp h.2⟩
  have small := CentralSteeperNegativeBottom.small_bottom (q 0) (q 5) r os on an
    (by rw [shape,shape,p.congruent,p.congruent])
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent 0 x y).mp h)) oMarker
    ((equivalent 0 _ _).mpr anchors.near_point) ((equivalent 0 _ _).mpr anchors.lower_point)
    (fun h => missingCorner ((equivalent 0 _ _).mp h)) oMissing
    ((equivalent 5 _ _).mpr data.1) ((equivalent 5 _ _).mpr data.2.1)
    sharpen.1.le sharpen.2 caps.2 apart
  exact C977NextBottomWall.excludes_of_small_bottom p hf (q 0) r os on small.le
    (shape 0) (equivalent 0) missingCorner

theorem bottom_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonical : ∀ i, 0<(q i).c ∧ |(q i).s|≤(q i).c)
    (an : Normal (q 5).c (q 5).s) (t : ℝ)
    (signed : (q 6).s=-t) (bn : Normal (q 6).c t)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (capU : (q 6).loU+(q 6).side≤3*(q 6).c-t) : 0<(q 0).s := by
  by_contra no
  have negative : (q 0).s≤0 := le_of_not_gt no
  have on : Normal (q 0).c (-(q 0).s) :=
    ⟨neg_nonneg.mpr negative,
      by simpa only [abs_of_nonpos negative] using (canonical 0).2,
      by nlinarith only [(q 0).unit_normal]⟩
  exact negative_bottom_excludes p hf q shape equivalent canonical an t (-(q 0).s)
    signed bn (by ring) on missingCorner center capU

#print axioms frame_sharpen
#print axioms negative_bottom_excludes
#print axioms bottom_positive
end N12Compact.C977NegativeNeighbor
