import Compact.Completion.C1092.MPPMInwardFinalBottomPositive
import Compact.Completion.C1092.MPPMInwardFinalBottomNegative

/-! INWARD-BOTTOM-ANGLE, Theorem 1. The frame chosen below only
reindexes the same actual B, preserving both its center and interior.
The actual-family producers of the sharp point and wall reach remain
separate obligations of the original-packing application. Source only.
-/
namespace N12Compact.C1092MPPMInwardFinal.BottomAngle
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

private theorem canonical_center_frame (B : OpenSquare) :
    ∃ D : OpenSquare,0<D.c ∧ |D.s|≤D.c ∧ D.side=B.side ∧
      centerX D=centerX B ∧ (∀ x y,D.Inside x y ↔ B.Inside x y) := by
  obtain ⟨D,dc,ds,same,cx,cy,inside⟩ := exists_positive_frame B
  by_cases order : D.s≤D.c
  · have cp : 0<D.c := by nlinarith only [D.unit_normal,dc,ds,order]
    exact ⟨D,cp,by simpa only [abs_of_nonneg ds] using order,same,cx,inside⟩
  · refine ⟨turnFrame (turnFrame (turnFrame D)),?_,?_,by simpa using same,
      by simpa using cx,?_⟩
    · simpa [turnFrame] using (show 0<D.s by linarith only [dc,order])
    · simpa [turnFrame,abs_of_nonneg dc] using (lt_of_not_ge order).le
    · intro x y; simpa using inside x y

theorem polynomial (C B : OpenSquare) (h : Input C B) :
    0<(half C.c (-C.s))^2-2*half C.c (-C.s)+1/5 := by
  apply lt_of_not_ge
  intro bad
  obtain ⟨D,dp,canonical,same,center,inside⟩ := canonical_center_frame B
  have input : Input C D :=
    { side := h.side
      same := h.same.trans same.symm
      normal := h.normal
      marker := h.marker
      inner := h.inner
      forward := h.forward
      crosspoint := h.crosspoint
      sharp := h.sharp
      origin := h.origin
      outer := h.outer
      bottomMarker := (inside _ _).mpr h.bottomMarker
      bottomNear := (inside _ _).mpr h.bottomNear
      bottomFar := (inside _ _).mpr h.bottomFar
      wall := fun x y own => h.wall x y ((inside x y).mp own)
      center := by rw [center]; exact h.center
      apart := fun x y own => h.apart x y ⟨own.1,(inside x y).mp own.2⟩ }
  by_cases positive : 0≤D.s
  · have dn : Normal D.c D.s :=
      ⟨positive,by simpa only [abs_of_nonneg positive] using canonical,D.unit_normal⟩
    exact nonnegative_impossible C D input dn bad
  · have negative : D.s≤0 := (lt_of_not_ge positive).le
    have dn : Normal D.c (-D.s) :=
      ⟨by linarith only [negative],by simpa only [abs_of_nonpos negative] using canonical,
        by nlinarith only [D.unit_normal]⟩
    exact nonpositive_impossible C D input dn bad

/-- Exact strict half-angle ceiling for the G-omitted missing-center
inward branch. No upper bound on the common side has been added. -/
theorem angle (C B : OpenSquare) (h : Input C B) :
    0<half C.c (-C.s) ∧ half C.c (-C.s)<1-2*Real.sqrt 5/5 ∧
      half C.c (-C.s)<53/500 := by
  have faces := central_faces C B h
  have cb := normal_bounds h.normal
  have positive : 0<half C.c (-C.s) := div_pos
    (by linarith only [faces.negative]) (by linarith only [cb.1])
  have result := threshold h.normal (polynomial C B h)
  exact ⟨positive,result⟩

#print axioms polynomial
#print axioms angle
end N12Compact.C1092MPPMInwardFinal.BottomAngle
