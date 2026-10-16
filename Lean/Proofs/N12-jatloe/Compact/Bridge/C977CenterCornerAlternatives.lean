import Compact.Bridge.C977CenterRightChain
import Compact.Geometry.CentralRightCornerAlternatives
import Compact.Geometry.CentralRightIncomingPositive
import Compact.Geometry.CentralRightIncomingOrdered

/-! Actual original corner alternatives for the center-owned, B-owned
incoming central axis. Every B/R sign is retained; negative B's lower-V
escape is transported to the real right-wall displacement. -/
namespace N12Compact.C977CenterCornerAlternatives

open S12 S12Pilot S12Completion.C977 FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic
set_option Elab.async false

private theorem right_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 10)).Inside (1543/500) 2 ∧
    (p.square (orderedOwner p 10)).Inside 3 (12/5) := by
  have markers := coded_exact p (orderedOwner p 10)
  rw [ordered_owner_code p hf 10] at markers
  constructor
  · have point := (markers 14).mpr (by decide)
    simpa [Owns,marker] using point
  · have check : ∀ owned∈pruningDomain4 10, 19∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 10)
    have point := (nat_combined_exact p (orderedOwner p 10) 19 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point

private theorem corner_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 3)).Inside (1543/500) 3 ∧
    (p.square (orderedOwner p 3)).Inside 3 (1543/500) := by
  have markers := coded_exact p (orderedOwner p 3)
  rw [ordered_owner_code p hf 3] at markers
  constructor
  · have point := (markers 5).mpr (by decide)
    simpa [Owns,marker] using point
  · have point := (markers 4).mpr (by decide)
    simpa [Owns,marker] using point

/-- The real nonpositive right wall owns the inward point, independently
of central ownership or any central separating-axis choice. -/
theorem negative_wall_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (R : OpenSquare) (t : ℝ) (normal : Normal R.c t) (signed : R.s=-t)
    (shape : R.side=(p.square (orderedOwner p 10)).side)
    (equivalent : ∀ x y, R.Inside x y↔(p.square (orderedOwner p 10)).Inside x y) :
    R.Inside 3 2 := by
  have rd := right_data p hf
  have ed := corner_data p hf
  exact PairedCornerPositiveWall.negative_right_point R _ t signed normal
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent x y).mp h))
    ((equivalent _ _).mpr rd.1) ((equivalent _ _).mpr rd.2)
    (C977CenterRightChain.corner_outward p hf)
    (C977RightCornerSupport.northeast_corner p hf) ed.1 ed.2
    (fun x y h => p.disjoint _ _ (fun eq => (by decide : (3 : Fin 12)≠10)
      (ordered_owner_injective p hf eq)) x y ⟨h.1,(equivalent x y).mp h.2⟩)

/-- Negative B needs no conditional inner auxiliary point. Its actual
corner exclusion has two faces; both are retained by the conclusion. -/
theorem negative_frame_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (bn : Normal (q 6).c t) (signed : (q 6).s=-t)
    (canonicalR : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU) :
    (q 6).loU+(q 6).side≤3*(q 6).c-t ∨
      (0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s≤(q 10).loU) := by
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have missing : ¬(q 6).Inside 3 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠2) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977RightCornerSupport.southeast_corner p hf⟩
  have rd := right_data p hf
  have ed := corner_data p hf
  have br : ∀ x y, ¬((q 6).Inside x y ∧ (q 10).Inside x y) := by
    intro x y h
    exact p.disjoint _ _ (fun eq => (by decide : (6 : Fin 12)≠10)
      (ordered_owner_injective p hf eq)) x y
      ⟨(equivalent 6 _ _).mp h.1,(equivalent 10 _ _).mp h.2⟩
  have er : ∀ x y, ¬((p.square (orderedOwner p 3)).Inside x y ∧ (q 10).Inside x y) := by
    intro x y h
    exact p.disjoint _ _ (fun eq => (by decide : (3 : Fin 12)≠10)
      (ordered_owner_injective p hf eq)) x y ⟨h.1,(equivalent 10 _ _).mp h.2⟩
  have aCenter := (equivalent 5 _ _).mpr center
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s
    (q 6).unit_normal aCenter).2
  exact CentralRightCornerAlternatives.alternatives (q 6) (q 10) _ t bn signed canonicalR
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent 10 x y).mp h)) bMarker missing
    ((equivalent 10 _ _).mpr rd.1) ((equivalent 10 _ _).mpr rd.2)
    (C977CenterRightChain.corner_outward p hf)
    (C977RightCornerSupport.northeast_corner p hf) ed.1 ed.2 br er
    (by nlinarith only [strict,incoming,signed])

/-- All signed canonical B/R frames for this incoming central axis.
The positive-B branch alone requires its original conditional inner16. -/
theorem canonical_frame_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonicalB : |(q 6).s|≤(q 6).c) (canonicalR : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (inner : 0≤(q 6).s → (p.square (orderedOwner p 6)).Inside (113/50) 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU) :
    ((q 6).s≤0 ∧ (q 6).loU+(q 6).side≤3*(q 6).c+(q 6).s) ∨
      (0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s≤(q 10).loU) := by
  by_cases sign : 0≤(q 6).s
  · have bn : Normal (q 6).c (q 6).s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalB,(q 6).unit_normal⟩
    have shift := C977CenterRightChain.canonical_frame_shift p hf q shape equivalent
      bn canonicalR center (inner sign) incoming
    exact Or.inr ⟨shift.1,shift.2.le⟩
  · have negative : (q 6).s<0 := lt_of_not_ge sign
    have bn : Normal (q 6).c (-(q 6).s) :=
      ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonicalB,
        by nlinarith only [(q 6).unit_normal]⟩
    rcases negative_frame_alternatives p hf q shape equivalent (-(q 6).s) bn
      (by ring) canonicalR center incoming with cap | shift
    · exact Or.inl ⟨negative.le,by linarith only [cap]⟩
    · exact Or.inr shift

/-- Preferred complete signed reduction. The actual outer low point
removes the inner16 premise in every central orientation. -/
theorem all_frame_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonicalB : |(q 6).s|≤(q 6).c) (canonicalR : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : upper (q 5) (q 6).c (q 6).s≤(q 6).loU) :
    ((q 6).s<0 ∧ (q 6).loU+(q 6).side≤3*(q 6).c+(q 6).s) ∨
      (0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s≤(q 10).loU) := by
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have bLow : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have missing : ¬(q 6).Inside 3 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠2) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977RightCornerSupport.southeast_corner p hf⟩
  have rd := right_data p hf
  have ed := corner_data p hf
  have br : ∀ x y, ¬((q 6).Inside x y ∧ (q 10).Inside x y) := by
    intro x y h
    exact p.disjoint _ _ (fun eq => (by decide : (6 : Fin 12)≠10)
      (ordered_owner_injective p hf eq)) x y
      ⟨(equivalent 6 _ _).mp h.1,(equivalent 10 _ _).mp h.2⟩
  have er : ∀ x y, ¬((p.square (orderedOwner p 3)).Inside x y ∧ (q 10).Inside x y) := by
    intro x y h
    exact p.disjoint _ _ (fun eq => (by decide : (3 : Fin 12)≠10)
      (ordered_owner_injective p hf eq)) x y ⟨h.1,(equivalent 10 _ _).mp h.2⟩
  have strict := (strict_bounds (q 5) 2 2 (q 6).c (q 6).s (q 6).unit_normal
    ((equivalent 5 _ _).mpr center)).2
  exact CentralRightCornerAlternatives.canonical_alternatives (q 6) (q 10) _
    canonicalB canonicalR
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (by rw [shape,p.congruent]; exact p.side_gt_one)
    (fun x y h => p.contained _ x y ((equivalent 10 x y).mp h)) bMarker bLow missing
    ((equivalent 10 _ _).mpr rd.1) ((equivalent 10 _ _).mpr rd.2)
    (C977CenterRightChain.corner_outward p hf)
    (C977RightCornerSupport.northeast_corner p hf) ed.1 ed.2 br er
    (by linarith only [strict,incoming])

/-- The positive A-owned incoming axis and negative B sign have the same
genuine two-outcome reduction. Its remaining corner cap is explicit;
it is not substituted into a theorem requiring a B-owned incoming axis. -/
theorem positive_axis_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (t : ℝ) (an : Normal (q 5).c (q 5).s) (bn : Normal (q 6).c t)
    (signed : (q 6).s=-t) (canonicalR : |(q 10).s|≤(q 10).c)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : (q 5).loU+(q 5).side≤lower (q 6) (q 5).c (q 5).s) :
    (q 6).loU+(q 6).side≤3*(q 6).c-t ∨
      (0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s≤(q 10).loU) := by
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have bLow : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have missingCorner : ¬(q 6).Inside 3 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠2) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977RightCornerSupport.southeast_corner p hf⟩
  rcases CentralRightCornerAlternatives.corner_faces (q 6) t bn signed bMarker
      missingCorner with cap | escape
  · exact Or.inl cap
  · have aCenter := (equivalent 5 _ _).mpr center
    have point := CentralRightIncomingPositive.lower_escape_point (q 6) t an bn signed
      (by rw [shape,p.congruent]; exact p.side_gt_one) bMarker bLow escape
      (by linarith only [aCenter.2.1,incoming])
    have missing : ¬(q 10).Inside 3 2 := fun h => p.disjoint _ _
      (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
      ⟨(equivalent 6 _ _).mp point,(equivalent 10 _ _).mp h⟩
    right
    by_cases sign : 0≤(q 10).s
    · have rn : Normal (q 10).c (q 10).s :=
        ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalR,(q 10).unit_normal⟩
      have rd := right_data p hf
      exact ⟨sign,CentralRightCornerAlternatives.positive_wall_missing (q 10) rn
        ((equivalent 10 _ _).mpr rd.1) ((equivalent 10 _ _).mpr rd.2) missing⟩
    · have negative : (q 10).s<0 := lt_of_not_ge sign
      have rn : Normal (q 10).c (-(q 10).s) :=
        ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonicalR,
          by nlinarith only [(q 10).unit_normal]⟩
      exact False.elim (missing (negative_wall_point p hf (q 10) (-(q 10).s) rn
        (by ring) (shape 10) (equivalent 10)))

/-- The A-owned axis has the same complete corner/outer-wall reduction
whenever A's signed angle is at least B's. The comparison is homogeneous
and retains both genuine southeast-corner faces. -/
theorem ordered_axis_alternatives (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (q : Fin 12→OpenSquare)
    (shape : ∀ i, (q i).side=(p.square (orderedOwner p i)).side)
    (equivalent : ∀ i x y, (q i).Inside x y↔(p.square (orderedOwner p i)).Inside x y)
    (canonicalA : |(q 5).s|≤(q 5).c) (canonicalB : |(q 6).s|≤(q 6).c)
    (canonicalR : |(q 10).s|≤(q 10).c)
    (order : 0≤(q 5).s*(q 6).c-(q 5).c*(q 6).s)
    (center : (p.square (orderedOwner p 5)).Inside 2 2)
    (incoming : (q 5).loU+(q 5).side≤lower (q 6) (q 5).c (q 5).s) :
    ((q 6).s<0 ∧ (q 6).loU+(q 6).side≤3*(q 6).c+(q 6).s) ∨
      (0≤(q 10).s ∧ 3*(q 10).c+2*(q 10).s≤(q 10).loU) := by
  have bm := coded_exact p (orderedOwner p 6)
  rw [ordered_owner_code p hf 6] at bm
  have bMarker : (q 6).Inside (47/20) (33/20) := (equivalent 6 _ _).mpr (by
    have point := (bm 9).mpr (by decide)
    simpa [Owns,marker] using point)
  have bLow : (q 6).Inside 3 (87/50) := (equivalent 6 _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 6, 8∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 6)
    have point := (nat_combined_exact p (orderedOwner p 6) 8 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have bSide : 1<(q 6).side := by rw [shape,p.congruent]; exact p.side_gt_one
  have aCenter := (equivalent 5 _ _).mpr center
  have strict : 2*((q 5).c+(q 5).s)<lower (q 6) (q 5).c (q 5).s := by
    linarith only [aCenter.2.1,incoming]
  have missingCorner : ¬(q 6).Inside 3 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (6 : Fin 12)≠2) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent 6 _ _).mp h,C977RightCornerSupport.southeast_corner p hf⟩
  rcases CentralRightCornerAlternatives.canonical_corner_faces (q 6) canonicalB
      bMarker missingCorner with cap | escape
  · left
    refine ⟨?_,cap⟩
    by_contra no
    have nonnegative : 0≤(q 6).s := le_of_not_gt no
    have pointCap : (q 6).loU+(q 6).side≤3*(q 6).c+2*(q 6).s := by
      linarith only [cap,nonnegative]
    have bound := CentralRightIncomingOrdered.upper_u_bound (q 6) canonicalA canonicalB
      order bSide.le bMarker pointCap
    linarith only [strict,bound]
  · have point := CentralRightIncomingOrdered.lower_escape_point (q 6)
      canonicalA canonicalB order bSide bMarker bLow escape strict
    have missing : ¬(q 10).Inside 3 2 := fun h => p.disjoint _ _
      (fun eq => (by decide : (6 : Fin 12)≠10) (ordered_owner_injective p hf eq)) _ _
      ⟨(equivalent 6 _ _).mp point,(equivalent 10 _ _).mp h⟩
    right
    by_cases sign : 0≤(q 10).s
    · have rn : Normal (q 10).c (q 10).s :=
        ⟨sign,by simpa only [abs_of_nonneg sign] using canonicalR,(q 10).unit_normal⟩
      have rd := right_data p hf
      exact ⟨sign,CentralRightCornerAlternatives.positive_wall_missing (q 10) rn
        ((equivalent 10 _ _).mpr rd.1) ((equivalent 10 _ _).mpr rd.2) missing⟩
    · have negative : (q 10).s<0 := lt_of_not_ge sign
      have rn : Normal (q 10).c (-(q 10).s) :=
        ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonicalR,
          by nlinarith only [(q 10).unit_normal]⟩
      exact False.elim (missing (negative_wall_point p hf (q 10) (-(q 10).s) rn
        (by ring) (shape 10) (equivalent 10)))

#print axioms negative_wall_point
#print axioms negative_frame_alternatives
#print axioms canonical_frame_alternatives
#print axioms all_frame_alternatives
#print axioms positive_axis_alternatives
#print axioms ordered_axis_alternatives
end N12Compact.C977CenterCornerAlternatives
