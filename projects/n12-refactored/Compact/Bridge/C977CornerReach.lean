import Compact.Bridge.C977CentralReach
import Compact.Geometry.SouthwestCornerTranspose

/-! Original-family entrance to the completed continuous corner sectors.
This preserves the one remaining sign/incidence case explicitly; it does
not claim an entire representative or ownership vector is excluded. -/
namespace N12Compact.C977CornerReach

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (i j : Fin 12) (different : i ≠ j) :
    ∀ x y, ¬ ((p.square (orderedOwner p i)).Inside x y ∧
      (p.square (orderedOwner p j)).Inside x y) := by
  apply p.disjoint
  exact fun h => different (ordered_owner_injective p hf h)

/-- With the bottom singleton chosen to miss its corner, every canonical
central frame either owns (2,2), or is strictly positive and the left
singleton owns the corner. All owned and excluded points are recovered
from the original family, including both new strict central crosspoints. -/
theorem frame_point_or_left_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family)
    (missing : ¬ (p.square (orderedOwner p 0)).Inside 1 1)
    (A : OpenSquare) (canonical : |A.s| ≤ A.c)
    (shape : A.side = (p.square (orderedOwner p 5)).side)
    (inside : ∀ x y, A.Inside x y ↔ (p.square (orderedOwner p 5)).Inside x y) :
    (p.square (orderedOwner p 5)).Inside 2 2 ∨
      (0 < A.s ∧ (p.square (orderedOwner p 1)).Inside 1 1) := by
  obtain ⟨pP,pD,pE,_,_,_⟩ := C977CentralReach.central_data p hf
  have new := C977CentralReach.central_points p hf
  have aP := (inside _ _).mpr pP
  have aD := (inside _ _).mpr pD
  have aE := (inside _ _).mpr pE
  have aLow := (inside _ _).mpr new.1
  have aLeft := (inside _ _).mpr new.2
  have side : 1 < A.side := by rw [shape,p.congruent]; exact p.side_gt_one
  have sameO : (p.square (orderedOwner p 0)).side=A.side := by
    simp only [shape,p.congruent]
  have sameL : (p.square (orderedOwner p 1)).side=A.side := by
    simp only [shape,p.congruent]
  have oAnchors := code_one_anchors p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0)
  have lAnchors := code_two_original_anchors p (orderedOwner p 1)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 1)
  have oMarkers := coded_exact p (orderedOwner p 0)
  rw [ordered_owner_code p hf 0] at oMarkers
  have lMarkers := coded_exact p (orderedOwner p 1)
  rw [ordered_owner_code p hf 1] at lMarkers
  have oM : (p.square (orderedOwner p 0)).Inside 1 (457/500) := by
    have h := (oMarkers 0).mpr (by decide)
    simpa [Owns,marker] using h
  have lM : (p.square (orderedOwner p 1)).Inside (457/500) 1 := by
    have h := (lMarkers 1).mpr (by decide)
    simpa [Owns,marker] using h
  have oMissing : ¬ (p.square (orderedOwner p 0)).Inside 2 (457/500) := by
    intro h
    have absent : (13 : Marker) ∉ maskSupport (auxiliaryCode 0) := by decide
    exact absent ((oMarkers 13).mp (by simpa [Owns,marker] using h))
  have lMissing : ¬ (p.square (orderedOwner p 1)).Inside (457/500) 2 := by
    intro h
    have absent : (12 : Marker) ∉ maskSupport (auxiliaryCode 1) := by decide
    exact absent ((lMarkers 12).mp (by simpa [Owns,marker] using h))
  have oa : ∀ x y, ¬ ((p.square (orderedOwner p 0)).Inside x y ∧ A.Inside x y) :=
    fun x y h => apart p hf 0 5 (by decide) x y ⟨h.1,(inside x y).mp h.2⟩
  have al : ∀ x y, ¬ (A.Inside x y ∧ (p.square (orderedOwner p 1)).Inside x y) :=
    fun x y h => apart p hf 5 1 (by decide) x y ⟨(inside x y).mp h.1,h.2⟩
  by_cases negative : A.s ≤ 0
  · have normal : Normal A.c (-A.s) := ⟨by linarith only [negative],
      by simpa only [abs_of_nonpos negative] using canonical,
      by nlinarith only [A.unit_normal]⟩
    have point := SouthwestNegativeCorner.point _ A _ (-A.s) (by ring) normal
      sameO side (p.contained _) oM oAnchors.near_point oAnchors.lower_point
      missing oMissing aP aD aE aLeft lAnchors.1 lAnchors.2.1 oa al
    exact Or.inl ((inside 2 2).mp point)
  · have positive : 0 < A.s := lt_of_not_ge negative
    by_cases corner : (p.square (orderedOwner p 1)).Inside 1 1
    · exact Or.inr ⟨positive,corner⟩
    · have normal : Normal A.c A.s := ⟨positive.le,
        by simpa only [abs_of_pos positive] using canonical,A.unit_normal⟩
      have point := SouthwestCornerTranspose.point _ A _ normal sameL side
        (p.contained _) lM lAnchors.1 lAnchors.2.2 corner lMissing
        aP aD aE aLow oAnchors.near_point oAnchors.horizontal_point
        (fun x y h => al x y ⟨h.2,h.1⟩)
        (fun x y h => oa x y ⟨h.2,h.1⟩)
      exact Or.inl ((inside 2 2).mp point)

/-- Exact residual orientation/incidence cover in the original packing.
The remaining positive-central/left-corner branch is not excluded here. -/
theorem central_point_or_positive_corner (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family)
    (missing : ¬ (p.square (orderedOwner p 0)).Inside 1 1) :
    (p.square (orderedOwner p 5)).Inside 2 2 ∨
      ∃ A : OpenSquare, 0 < A.s ∧ A.s ≤ A.c ∧
        A.side = (p.square (orderedOwner p 5)).side ∧
        (∀ x y, A.Inside x y ↔ (p.square (orderedOwner p 5)).Inside x y) ∧
        (p.square (orderedOwner p 1)).Inside 1 1 := by
  obtain ⟨A,_,canonical,shape,inside,_⟩ :=
    ClosedFrames.canonical_frame (p.square (orderedOwner p 5))
  rcases frame_point_or_left_corner p hf missing A canonical shape inside with point | h
  · exact Or.inl point
  · exact Or.inr ⟨A,h.1,by simpa only [abs_of_pos h.1] using canonical,
      shape,inside,h.2⟩

#print axioms central_point_or_positive_corner

end N12Compact.C977CornerReach
