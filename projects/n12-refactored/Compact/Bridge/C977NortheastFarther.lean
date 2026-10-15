import Compact.Bridge.C977CenterRightChain
import Compact.Geometry.UpperRightCornerTopLongitudinal
import Compact.Geometry.UpperRightNegativeTopReach
import Compact.Geometry.UpperRightNegativeCornerPositiveTop
import Compact.Geometry.UpperRightNegativePairReach
import Compact.Geometry.RightWallOuterSegment

/-! Actual C977 northeast-pair reach for a positive canonical corner,
with both top-wall signs retained. The foreign right-wall point and top
wing are supplied by their genuine original owners. Source only. -/
namespace N12Compact.C977NortheastFarther

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

/-- The strict points and full-square relations of the same original
corner/top pair, shared by all signed endpoint arguments. -/
structure FrameData (E T : OpenSquare) : Prop where
  side : 1<E.side
  same : E.side=T.side
  eBox : InsideContainer E
  tBox : InsideContainer T
  corner : E.Inside 3 3
  outward : E.Inside (16/5) 3
  missingRight : ¬E.Inside 3 (12/5)
  marker : T.Inside 2 (1543/500)
  row : T.Inside (12/5) 3
  missingWing : ¬T.Inside (87/50) 3
  missingNE : ¬T.Inside (47/20) (47/20)
  apart : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y)

theorem frame_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (E T : OpenSquare)
    (eShape : E.side=(p.square (orderedOwner p 3)).side)
    (tShape : T.side=(p.square (orderedOwner p 11)).side)
    (eEquivalent : ∀ x y, E.Inside x y↔(p.square (orderedOwner p 3)).Inside x y)
    (tEquivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside x y) :
    FrameData E T := by
  have side : 1<E.side := by rw [eShape,p.congruent]; exact p.side_gt_one
  have same : E.side=T.side := by rw [eShape,tShape,p.congruent,p.congruent]
  have eBox : InsideContainer E :=
    fun x y h => p.contained _ x y ((eEquivalent x y).mp h)
  have tBox : InsideContainer T :=
    fun x y h => p.contained _ x y ((tEquivalent x y).mp h)
  have corner := (eEquivalent _ _).mpr (C977RightCornerSupport.northeast_corner p hf)
  have outward := (eEquivalent _ _).mpr (C977CenterRightChain.corner_outward p hf)
  have rightRow : (p.square (orderedOwner p 10)).Inside 3 (12/5) := by
    have check : ∀ owned∈pruningDomain4 10, 19∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 10)
    have point := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have missingRight : ¬E.Inside 3 (12/5) := fun h =>
    apart p hf 3 10 (by decide) _ _ ⟨(eEquivalent _ _).mp h,rightRow⟩
  have tm := coded_exact p (orderedOwner p 11)
  rw [ordered_owner_code p hf 11] at tm
  have marker : T.Inside 2 (1543/500) := (tEquivalent _ _).mpr (by
    have point := (tm 15).mpr (by decide)
    simpa [Owns,marker] using point)
  have row : T.Inside (12/5) 3 := (tEquivalent _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 11, 7∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 11)
    have point := (nat_combined_exact p (orderedOwner p 11) 7 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have wing : (p.square (orderedOwner p 7)).Inside (87/50) 3 := by
    have check : ∀ owned∈pruningDomain4 7, 14∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 7)
    have point := (nat_combined_exact p (orderedOwner p 7) 14 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point
  have missingWing : ¬T.Inside (87/50) 3 := fun h =>
    apart p hf 11 7 (by decide) _ _ ⟨(tEquivalent _ _).mp h,wing⟩
  have missingNE : ¬T.Inside (47/20) (47/20) := by
    intro h
    have missing := unused_marker_ten p hf (orderedOwner p 11)
    apply missing
    simpa [Owns,marker] using (tEquivalent _ _).mp h
  have separated : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y) :=
    fun x y h => apart p hf 3 11 (by decide) x y
      ⟨(eEquivalent x y).mp h.1,(tEquivalent x y).mp h.2⟩
  exact ⟨side,same,eBox,tBox,corner,outward,missingRight,marker,row,
    missingWing,missingNE,separated⟩

/-- A positive canonical representative of the actual northeast owner
reaches the farther point, regardless of the canonical top-wall sign. -/
theorem frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (E T : OpenSquare) (en : Normal E.c E.s) (tn : |T.s|≤T.c)
    (eShape : E.side=(p.square (orderedOwner p 3)).side)
    (tShape : T.side=(p.square (orderedOwner p 11)).side)
    (eEquivalent : ∀ x y, E.Inside x y↔(p.square (orderedOwner p 3)).Inside x y)
    (tEquivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside x y) :
    E.Inside (7/2) 3 := by
  rcases frame_data p hf E T eShape tShape eEquivalent tEquivalent with
    ⟨side,same,eBox,tBox,corner,outward,missingRight,marker,row,
      missingWing,missingNE,separated⟩
  by_cases sign : 0≤T.s
  · have normal : Normal T.c T.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using tn,T.unit_normal⟩
    exact UpperRightCornerTopLongitudinal.point E T en normal same side eBox
      corner outward missingRight marker row missingWing missingNE separated
  · have negative : T.s≤0 := (lt_of_not_ge sign).le
    have normal : Normal T.c (-T.s) :=
      ⟨neg_nonneg.mpr negative,by simpa only [abs_of_nonpos negative] using tn,
        by nlinarith only [T.unit_normal]⟩
    exact UpperRightNegativeTopReach.point E T (-T.s) (by ring) en normal
      same side eBox tBox corner outward missingRight marker row
      missingWing missingNE separated

/-- The complementary negative-corner/positive-top sector uses the
genuine vertical endpoint supplied by the diagonal original-family argument. -/
theorem negative_frame_point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (E T : OpenSquare)
    (en : Normal E.c (-E.s)) (tn : Normal T.c T.s)
    (eShape : E.side=(p.square (orderedOwner p 3)).side)
    (tShape : T.side=(p.square (orderedOwner p 11)).side)
    (eEquivalent : ∀ x y, E.Inside x y↔(p.square (orderedOwner p 3)).Inside x y)
    (tEquivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside x y)
    (vertical : E.Inside 3 (7/2)) : E.Inside (7/2) 3 := by
  have d := frame_data p hf E T eShape tShape eEquivalent tEquivalent
  exact UpperRightNegativeCornerPositiveTop.point E T (-E.s) (by ring)
    en tn d.same d.side d.eBox d.corner d.outward vertical
    d.marker d.row d.missingWing d.missingNE d.apart

/-- The last signed pair uses the same original points and containers.
The vertical endpoint is supplied by the full packing's diagonal symmetry. -/
theorem negative_pair_frame_point (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (E T : OpenSquare)
    (en : Normal E.c (-E.s)) (tn : Normal T.c (-T.s))
    (eShape : E.side=(p.square (orderedOwner p 3)).side)
    (tShape : T.side=(p.square (orderedOwner p 11)).side)
    (eEquivalent : ∀ x y, E.Inside x y↔(p.square (orderedOwner p 3)).Inside x y)
    (tEquivalent : ∀ x y, T.Inside x y↔(p.square (orderedOwner p 11)).Inside x y)
    (vertical : E.Inside 3 (7/2)) : E.Inside (7/2) 3 := by
  have d := frame_data p hf E T eShape tShape eEquivalent tEquivalent
  exact UpperRightNegativePairReach.point E T (-E.s) (-T.s) (by ring) (by ring)
    en tn d.same d.side d.eBox d.tBox d.corner d.outward vertical
    d.marker d.row d.missingWing d.missingNE d.apart

/-- The actual farther corner point closes the full original right-wall
displacement, independently of which corner argument supplied the point. -/
theorem right_shift_of_farther (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (rn : Normal (q 10).c (q 10).s)
    (shift : 3*(q 10).c+2*(q 10).s≤(q 10).loU)
    (farther : (q 3).Inside (7/2) 3) : False := by
  have outward := (equivalent 3 _ _).mpr (C977CenterRightChain.corner_outward p hf)
  have rm := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at rm
  have marker : (q 10).Inside (1543/500) 2 := (equivalent 10 _ _).mpr (by
    have point := (rm 14).mpr (by decide)
    simpa [Owns,marker] using point)
  exact RightWallOuterSegment.impossible (q 10) (q 3) rn
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent 10 x y).mp h)) marker shift
    outward farther (fun x y h => apart p hf 3 10 (by decide) x y
      ⟨(equivalent 3 x y).mp h.1,(equivalent 10 x y).mp h.2⟩)

/-- Both top-wall signs and all E/T axes are included for a positive
northeast corner. -/
theorem right_shift_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (en : Normal (q 3).c (q 3).s) (tn : |(q 11).s|≤(q 11).c)
    (rn : Normal (q 10).c (q 10).s)
    (shift : 3*(q 10).c+2*(q 10).s≤(q 10).loU) : False := by
  exact right_shift_of_farther p hf q shape equivalent rn shift
    (frame_point p hf (q 3) (q 11) en tn
      (shape 3) (shape 11) (equivalent 3) (equivalent 11))

#print axioms frame_point
#print axioms right_shift_excludes
end N12Compact.C977NortheastFarther
