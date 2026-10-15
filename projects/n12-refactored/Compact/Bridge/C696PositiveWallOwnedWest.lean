import Compact.Bridge.C696WallCycle
import Compact.Geometry.CornerBudgetReach
import Compact.Geometry.PositiveWallOwnedWestCorner

/-! A complete original C696 orientation sector at each of the four walls.
If the adjacent central square owns the chart point (1,2), the wall cannot
have a positive canonical frame. The actual paired corner supplies its
outward triangle, using its empty original auxiliary assignment. All four
charts are applied to the same packing; no independent placement or 2.88
point is assumed. Source only, uncompiled. -/
namespace N12Compact.C696PositiveWallOwnedWest

open S12 S12Pilot S12Completion.C696 SideSignPacking C977CornerCubic
set_option Elab.async false

def cornerOwner : Fin 4 → Fin 12 := ![5,2,2,5]
def centralOwner : Fin 4 → Fin 12 := ![6,6,7,7]
def singletonOwner : Fin 4 → Fin 12 := ![1,0,4,3]

noncomputable def frame (q : OpenSquare) (i : Fin 4) : OpenSquare :=
  ![q,pullSwap q,pullX (pullY q),pullX (pullY (pullSwap q))] i

private theorem frame_inside (q : OpenSquare) (i : Fin 4) (P : ℚ×ℚ) :
    (frame q i).Inside P.1 P.2 ↔
      q.Inside (C696WallCycle.wallPoint i P).1 (C696WallCycle.wallPoint i P).2 := by
  fin_cases i <;>
    simp [frame,C696WallCycle.wallPoint,inside_pullX,inside_pullY,inside_pullSwap]

private theorem frame_side (q : OpenSquare) (i : Fin 4) :
    (frame q i).side=q.side := by fin_cases i <;> rfl

private theorem frame_box (q : OpenSquare) (box : InsideContainer q) (i : Fin 4) :
    InsideContainer (frame q i) := by
  fin_cases i
  · exact box
  · exact container_pullSwap q box
  · exact container_pullX _ (container_pullY q box)
  · exact container_pullX _ (container_pullY _ (container_pullSwap q box))

private theorem owners_apart (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (j k : Fin 12) (different : j≠k) :
    ∀ x y, ¬((owners p j).Inside x y ∧ (owners p k).Inside x y) := by
  apply p.disjoint
  intro equal
  have hj := ownerIndex_spec p (ownerMasks j) (by rw [hf]; exact ownerMasks_mem j)
  have hk := ownerIndex_spec p (ownerMasks k) (by rw [hf]; exact ownerMasks_mem k)
  exact different (AuxiliaryNecessity.ownerMasks_injective
    (hj.symm.trans ((congrArg (markerCode p) equal).trans hk)))

private theorem frame_apart (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (j k : Fin 12) (different : j≠k)
    (i : Fin 4) :
    ∀ x y, ¬((frame (owners p j) i).Inside x y ∧
      (frame (owners p k) i).Inside x y) := by
  have original := owners_apart p hf j k different
  intro x y h
  fin_cases i <;>
    simp [frame,inside_pullX,inside_pullY,inside_pullSwap] at h <;>
    exact original _ _ h

private theorem owned (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (role : Fin 4 → Fin 12) (P : ℚ×ℚ)
    (check : ∀ i, C696WallCycle.wallPoint i P∈
      queryInsidePoints (ownerMasks (role i)) 2 (auxiliaryVector (role i)))
    (i : Fin 4) : (frame (owners p (role i)) i).Inside P.1 P.2 :=
  (frame_inside _ i P).mpr (C696WallCycle.inside_query p hf _ _ (check i))

private theorem missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (role : Fin 4 → Fin 12) (P : ℚ×ℚ)
    (check : ∀ i, C696WallCycle.wallPoint i P∈
      queryOutsidePoints (ownerMasks (role i)) 2 (auxiliaryVector (role i)))
    (i : Fin 4) : ¬(frame (owners p (role i)) i).Inside P.1 P.2 :=
  fun h => C696WallCycle.outside_query p hf _ _ (check i) ((frame_inside _ i P).mp h)

/-- Each paired corner has empty original auxiliary assignment. Its two
genuine excluded points therefore force the outward point, without any
assumption about the opposite central or singleton orientation. -/
theorem corner_outward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) : (frame (owners p (cornerOwner i)) i).Inside (4/5) 3 := by
  have top : (frame (owners p (cornerOwner i)) i).Inside 1 (1543/500) := by
    simpa using owned p hf cornerOwner ((1,1543/500):ℚ×ℚ) (by decide +kernel) i
  have left : (frame (owners p (cornerOwner i)) i).Inside (457/500) 3 := by
    simpa using owned p hf cornerOwner ((457/500,3):ℚ×ℚ) (by decide +kernel) i
  have right : ¬(frame (owners p (cornerOwner i)) i).Inside (8/5) 3 := by
    simpa using missing p hf cornerOwner ((8/5,3):ℚ×ℚ) (by decide +kernel) i
  have below : ¬(frame (owners p (cornerOwner i)) i).Inside 1 (12/5) := by
    simpa using missing p hf cornerOwner ((1,12/5):ℚ×ℚ) (by decide +kernel) i
  exact CornerBudgetReach.upper_left _
    (by rw [frame_side]; exact C696WallCycle.side_gt p _)
    (frame_box _ (p.contained _) i) top left right below

/-- The actual wall frame has the two genuine V faces and strict small
positive tilt whenever the adjacent central square owns (1,2). -/
private theorem faces_of_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(owners p (C696WallCycle.wallOwner i)).side)
    (equivalent : ∀ x y, W.Inside x y↔
      (frame (owners p (C696WallCycle.wallOwner i)) i).Inside x y)
    (missingWest : ¬W.Inside 1 2) :
    2*W.c-W.s≤W.loV ∧ W.loV+W.side≤3*W.c-(457/500)*W.s ∧
      0<W.s ∧ W.s<43/250 := by
  have side : 1<W.side := by rw [shape]; exact C696WallCycle.side_gt p _
  have box : InsideContainer W := fun x y h =>
    frame_box _ (p.contained _) i x y ((equivalent x y).mp h)
  have marker : W.Inside (457/500) 2 := (equivalent _ _).mpr (by
    simpa using owned p hf C696WallCycle.wallOwner
      ((457/500,2):ℚ×ℚ) (by decide +kernel) i)
  have high : W.Inside 1 (12/5) := (equivalent _ _).mpr (by
    simpa using owned p hf C696WallCycle.wallOwner
      ((1,12/5):ℚ×ℚ) (by decide +kernel) i)
  have far : (frame (owners p (singletonOwner i)) i).Inside (19/25) (187/100) := by
    simpa using owned p hf singletonOwner ((19/25,187/100):ℚ×ℚ) (by decide +kernel) i
  have missingFar : ¬W.Inside (19/25) (187/100) := fun h =>
    frame_apart p hf (C696WallCycle.wallOwner i) (singletonOwner i)
      (by fin_cases i <;> decide) i _ _ ⟨(equivalent _ _).mp h,far⟩
  have topOriginal : ¬(frame (owners p (C696WallCycle.wallOwner i)) i).Inside
      (457/500) 3 := by
    simpa using missing p hf C696WallCycle.wallOwner ((457/500,3):ℚ×ℚ)
      (by decide +kernel) i
  have missingTop : ¬W.Inside (457/500) 3 := fun h =>
    topOriginal ((equivalent _ _).mp h)
  have outward := corner_outward p hf i
  have missingOut : ¬W.Inside (4/5) 3 := fun h =>
    frame_apart p hf (C696WallCycle.wallOwner i) (cornerOwner i)
      (by fin_cases i <;> decide) i _ _ ⟨(equivalent _ _).mp h,outward⟩
  have lower := PositiveWallOwnedWestFaces.lower_face W wn marker high missingWest
  have upper := PositiveWallOwnedWestFaces.upper_v W wn side box marker high
    missingWest missingFar missingTop missingOut
  have tilt := PositiveWallOwnedWestFaces.tilt wn side lower upper
  exact ⟨lower,upper,tilt.1,tilt.2⟩

/-- Every positive canonical wall in the actual family owns the inner
chart point itself. The original paired corner closes the entire
point-missing alternative without a central-square assumption. -/
theorem frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(owners p (C696WallCycle.wallOwner i)).side)
    (equivalent : ∀ x y, W.Inside x y↔
      (frame (owners p (C696WallCycle.wallOwner i)) i).Inside x y) :
    W.Inside 1 2 := by
  by_contra missingWest
  have side : 1<W.side := by rw [shape]; exact C696WallCycle.side_gt p _
  have box : InsideContainer W := fun x y h =>
    frame_box _ (p.contained _) i x y ((equivalent x y).mp h)
  have high : W.Inside 1 (12/5) := (equivalent _ _).mpr (by
    simpa using owned p hf C696WallCycle.wallOwner
      ((1,12/5):ℚ×ℚ) (by decide +kernel) i)
  have faces := faces_of_missing p hf i W wn shape equivalent missingWest
  have top : (frame (owners p (cornerOwner i)) i).Inside 1 (1543/500) := by
    simpa using owned p hf cornerOwner ((1,1543/500):ℚ×ℚ) (by decide +kernel) i
  have corner : (frame (owners p (cornerOwner i)) i).Inside 1 3 := by
    simpa using owned p hf cornerOwner ((1,3):ℚ×ℚ) (by decide +kernel) i
  exact PositiveWallOwnedWestCorner.impossible W _ wn side box high
    faces.1 faces.2.1 faces.2.2.1 faces.2.2.2
    (corner_outward p hf i) corner top
    (fun x y h => frame_apart p hf (cornerOwner i) (C696WallCycle.wallOwner i)
      (by fin_cases i <;> decide) i x y ⟨h.1,(equivalent x y).mp h.2⟩)

theorem frame_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(owners p (C696WallCycle.wallOwner i)).side)
    (equivalent : ∀ x y, W.Inside x y↔
      (frame (owners p (C696WallCycle.wallOwner i)) i).Inside x y)
    (west : (frame (owners p (centralOwner i)) i).Inside 1 2) :
    2*W.c-W.s≤W.loV ∧ W.loV+W.side≤3*W.c-(457/500)*W.s ∧
      0<W.s ∧ W.s<43/250 :=
  faces_of_missing p hf i W wn shape equivalent (fun h =>
    frame_apart p hf (C696WallCycle.wallOwner i) (centralOwner i)
      (by fin_cases i <;> decide) i _ _ ⟨(equivalent _ _).mp h,west⟩)

/-- An entire original C696 orientation cell, simultaneously at all four
walls. There is no sign hypothesis on either neighboring singleton. -/
theorem frame_excludes (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 4) (W : OpenSquare) (wn : Normal W.c W.s)
    (shape : W.side=(owners p (C696WallCycle.wallOwner i)).side)
    (equivalent : ∀ x y, W.Inside x y↔
      (frame (owners p (C696WallCycle.wallOwner i)) i).Inside x y)
    (west : (frame (owners p (centralOwner i)) i).Inside 1 2) : False := by
  have side : 1<W.side := by rw [shape]; exact C696WallCycle.side_gt p _
  have box : InsideContainer W := fun x y h =>
    frame_box _ (p.contained _) i x y ((equivalent x y).mp h)
  have high : W.Inside 1 (12/5) := (equivalent _ _).mpr (by
    simpa using owned p hf C696WallCycle.wallOwner
      ((1,12/5):ℚ×ℚ) (by decide +kernel) i)
  have faces := frame_faces p hf i W wn shape equivalent west
  have top : (frame (owners p (cornerOwner i)) i).Inside 1 (1543/500) := by
    simpa using owned p hf cornerOwner ((1,1543/500):ℚ×ℚ) (by decide +kernel) i
  have corner : (frame (owners p (cornerOwner i)) i).Inside 1 3 := by
    simpa using owned p hf cornerOwner ((1,3):ℚ×ℚ) (by decide +kernel) i
  exact PositiveWallOwnedWestCorner.impossible W _ wn side box high
    faces.1 faces.2.1 faces.2.2.1 faces.2.2.2
    (corner_outward p hf i) corner top
    (fun x y h => frame_apart p hf (cornerOwner i) (C696WallCycle.wallOwner i)
      (by fin_cases i <;> decide) i x y ⟨h.1,(equivalent x y).mp h.2⟩)

/-- Thus every signed canonical representative of the actual wall has
strictly negative sine in the owned-west branch, including exclusion of
the axis-parallel boundary. -/
theorem canonical_sine_negative (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (i : Fin 4) (W : OpenSquare)
    (canonical : |W.s|≤W.c)
    (shape : W.side=(owners p (C696WallCycle.wallOwner i)).side)
    (equivalent : ∀ x y, W.Inside x y↔
      (frame (owners p (C696WallCycle.wallOwner i)) i).Inside x y)
    (west : (frame (owners p (centralOwner i)) i).Inside 1 2) : W.s<0 := by
  apply lt_of_not_ge
  intro nonnegative
  exact frame_excludes p hf i W
    ⟨nonnegative,(le_abs_self W.s).trans canonical,W.unit_normal⟩
    shape equivalent west

#print axioms corner_outward
#print axioms frame_point
#print axioms frame_faces
#print axioms frame_excludes
#print axioms canonical_sine_negative
end N12Compact.C696PositiveWallOwnedWest
