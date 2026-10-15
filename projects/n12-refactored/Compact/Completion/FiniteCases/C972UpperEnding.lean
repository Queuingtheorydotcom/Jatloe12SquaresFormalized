import Compact.Completion.FiniteCases.C972NorthwestHalfpoint

/-! The missing NE top-origin branch is impossible. The remaining
configuration has a genuine NE-owned origin, NW halfpoint and left origin,
and the first singleton omits the shared lower corner. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem northeast_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 2 3 := by
  by_contra missing
  have h := fixed p hf
  rcases northwest_half_or_vertical p hf with half | vertical
  · have zero := zero_corner_of_southeast_halfpoint p hf
      (southeast_halfpoint_of_northeast_missing_origin p hf missing)
    have one : (owners p 1).Inside 1 1 := by
      by_contra absent
      exact left_missing_impossible p hf absent half
    exact apart p hf 0 1 (by decide) _ _ ⟨zero,one⟩
  · have point := C981CompletionUpperPoint.point _ (side p 7) h.northeastMarker
      (northeast_g7 p hf)
      (foreign p hf 7 8 (by decide) _ _ vertical.1) missing
      (foreign p hf 7 11 (by decide) _ _ h.rightG9)
      (foreign p hf 7 3 (by decide) _ _ h.northeastCorner)
      (foreign p hf 7 11 (by decide) _ _ (right_reach p hf))
    exact apart p hf 7 8 (by decide) _ _ ⟨point,vertical.2⟩

theorem northwest_outer_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside (3/2) 3 :=
  northwest_halfpoint_of_northeast_origin p hf (northeast_origin p hf)

theorem left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside 1 2 :=
  left_origin_of_northwest_halfpoint p hf (northwest_outer_halfpoint p hf)

theorem one_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 1).Inside 1 1 :=
  one_corner_of_northeast_origin p hf (northeast_origin p hf)

theorem zero_missing_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬(owners p 0).Inside 1 1 :=
  foreign p hf 0 1 (by decide) _ _ (one_corner p hf)

theorem southeast_missing_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    ¬(owners p 6).Inside 3 (3/2) := by
  intro half
  exact zero_missing_corner p hf (zero_corner_of_southeast_halfpoint p hf half)

end
#print axioms northeast_origin
#print axioms southeast_missing_halfpoint
end N12Compact.FiniteCases.C972
