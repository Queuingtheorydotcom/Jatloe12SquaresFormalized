import Compact.Bridge.C977OuterWings
import Compact.Geometry.CornerBudgetReach
import Compact.Geometry.PositiveWallOwnedWestCorner

/-! The original C977 upper pair has genuine outward reach because
the northwest central square owns the outer top wing. Together with
owned central (1,2), this bounds a positive left-wall frame on both
V faces. Its actual northeast vertex then enters the upper pair, closing
the entire positive-wall / owned-west cell independently of the bottom
orientation. These are full-packing consequences, not saved pose domains.
Source only, uncompiled. -/
namespace N12Compact.C977PositiveWallOwnedWest

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 12) (different : i≠j) :
    ∀ x y, ¬((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

private theorem wall_high (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 8)).Inside 1 (12/5) := by
  have check : ∀ owned ∈ pruningDomain4 8, 11∈owned := by decide
  have owned := check _ (pruned_auxiliary_domain_actual p hf 8)
  have point := (nat_combined_exact p (orderedOwner p 8) 11 (by decide)).mpr owned
  simpa [auxPoints,fPoints,gPoints] using point

/-- Original owner7's forced wing and owner8's original auxiliary point
provide the two exclusions needed by the full upper-corner square. -/
theorem corner_outward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (p.square (orderedOwner p 4)).Inside (4/5) 3 := by
  have markers := coded_exact p (orderedOwner p 4)
  rw [ordered_owner_code p hf 4] at markers
  have upper : (p.square (orderedOwner p 4)).Inside 1 (1543/500) := by
    have h := (markers 6).mpr (by decide)
    simpa [Owns,marker] using h
  have left : (p.square (orderedOwner p 4)).Inside (457/500) 3 := by
    have h := (markers 7).mpr (by decide)
    simpa [Owns,marker] using h
  have wing := (C977OuterWings.points p hf).2
  have high := wall_high p hf
  exact CornerBudgetReach.upper_left _
    (by rw [p.congruent]; exact p.side_gt_one) (p.contained _) upper left
    (fun h => apart p hf 4 7 (by decide) _ _ ⟨h,wing⟩)
    (fun h => apart p hf 4 8 (by decide) _ _ ⟨h,high⟩)

/-- Both positive-wall faces and its strict small tilt follow from the
original family once the southwest center owns the west point. The
paired-corner reach is derived internally, with no 2.88 premise. -/
private theorem faces_of_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(p.square (orderedOwner p 8)).side)
    (equivalent : ∀ x y, W.Inside x y↔(p.square (orderedOwner p 8)).Inside x y)
    (missingWest : ¬W.Inside 1 2) :
    2*W.c-W.s≤W.loV ∧ W.loV+W.side≤3*W.c-(457/500)*W.s ∧
      0<W.s ∧ W.s<43/250 := by
  have side : 1<W.side := by rw [shape,p.congruent]; exact p.side_gt_one
  have box : InsideContainer W :=
    fun x y h => p.contained _ x y ((equivalent x y).mp h)
  have markers := coded_exact p (orderedOwner p 8)
  rw [ordered_owner_code p hf 8] at markers
  have marker : W.Inside (457/500) 2 := (equivalent _ _).mpr (by
    have h := (markers 12).mpr (by decide)
    simpa [Owns,marker] using h)
  have high := (equivalent _ _).mpr (wall_high p hf)
  have lAnchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have missingFar : ¬W.Inside (19/25) (187/100) := fun h =>
    apart p hf 8 1 (by decide) _ _ ⟨(equivalent _ _).mp h,lAnchors.2.2⟩
  have missingTop : ¬W.Inside (457/500) 3 := by
    intro h
    have absent : (7 : Marker)∉maskSupport (auxiliaryCode 8) := by decide
    apply absent
    apply (markers 7).mp
    simpa [Owns,S12.marker] using (equivalent _ _).mp h
  have outward := corner_outward p hf
  have missingOut : ¬W.Inside (4/5) 3 := fun h =>
    apart p hf 8 4 (by decide) _ _ ⟨(equivalent _ _).mp h,outward⟩
  have lower := PositiveWallOwnedWestFaces.lower_face W wn marker high missingWest
  have upper := PositiveWallOwnedWestFaces.upper_v W wn side box marker high
    missingWest missingFar missingTop missingOut
  have tilt := PositiveWallOwnedWestFaces.tilt wn side lower upper
  exact ⟨lower,upper,tilt.1,tilt.2⟩

/-- The actual paired corner excludes the entire point-missing
alternative for every positive canonical wall frame. -/
theorem frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(p.square (orderedOwner p 8)).side)
    (equivalent : ∀ x y, W.Inside x y↔(p.square (orderedOwner p 8)).Inside x y) :
    W.Inside 1 2 := by
  by_contra missingWest
  have side : 1<W.side := by rw [shape,p.congruent]; exact p.side_gt_one
  have box : InsideContainer W :=
    fun x y h => p.contained _ x y ((equivalent x y).mp h)
  have high := (equivalent _ _).mpr (wall_high p hf)
  have faces := faces_of_missing p hf W wn shape equivalent missingWest
  have markers := coded_exact p (orderedOwner p 4)
  rw [ordered_owner_code p hf 4] at markers
  have top : (p.square (orderedOwner p 4)).Inside 1 (1543/500) := by
    have h := (markers 6).mpr (by decide)
    simpa [Owns,marker] using h
  have corner : (p.square (orderedOwner p 4)).Inside 1 3 := by
    have h := seed_points_sound (p.square (orderedOwner p 4))
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      _ markers ((1,3) : ℚ×ℚ) (by decide +kernel)
    simpa using h
  exact PositiveWallOwnedWestCorner.impossible W _ wn side box high
    faces.1 faces.2.1 faces.2.2.1 faces.2.2.2
    (corner_outward p hf) corner top
    (fun x y h => apart p hf 4 8 (by decide) x y
      ⟨h.1,(equivalent x y).mp h.2⟩)

theorem frame_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(p.square (orderedOwner p 8)).side)
    (equivalent : ∀ x y, W.Inside x y↔(p.square (orderedOwner p 8)).Inside x y)
    (west : (p.square (orderedOwner p 5)).Inside 1 2) :
    2*W.c-W.s≤W.loV ∧ W.loV+W.side≤3*W.c-(457/500)*W.s ∧
      0<W.s ∧ W.s<43/250 :=
  faces_of_missing p hf W wn shape equivalent (fun h =>
    apart p hf 8 5 (by decide) _ _ ⟨(equivalent _ _).mp h,west⟩)

/-- Original C977 cannot have a positive canonical left-wall frame while
the southwest center owns (1,2). The upper pair's full square, not just
an independent wall point, supplies the final disjointness contradiction. -/
theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(p.square (orderedOwner p 8)).side)
    (equivalent : ∀ x y, W.Inside x y↔(p.square (orderedOwner p 8)).Inside x y)
    (west : (p.square (orderedOwner p 5)).Inside 1 2) : False := by
  have side : 1<W.side := by rw [shape,p.congruent]; exact p.side_gt_one
  have box : InsideContainer W :=
    fun x y h => p.contained _ x y ((equivalent x y).mp h)
  have high := (equivalent _ _).mpr (wall_high p hf)
  have faces := frame_faces p hf W wn shape equivalent west
  have markers := coded_exact p (orderedOwner p 4)
  rw [ordered_owner_code p hf 4] at markers
  have top : (p.square (orderedOwner p 4)).Inside 1 (1543/500) := by
    have h := (markers 6).mpr (by decide)
    simpa [Owns,marker] using h
  have corner : (p.square (orderedOwner p 4)).Inside 1 3 := by
    have h := seed_points_sound (p.square (orderedOwner p 4))
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      _ markers ((1,3) : ℚ×ℚ) (by decide +kernel)
    simpa using h
  exact PositiveWallOwnedWestCorner.impossible W _ wn side box high
    faces.1 faces.2.1 faces.2.2.1 faces.2.2.2
    (corner_outward p hf) corner top
    (fun x y h => apart p hf 4 8 (by decide) x y
      ⟨h.1,(equivalent x y).mp h.2⟩)

#print axioms corner_outward
#print axioms frame_point
#print axioms frame_faces
#print axioms frame_excludes
end N12Compact.C977PositiveWallOwnedWest
