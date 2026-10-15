import Compact.Completion.FiniteCases.C972UpperReduction
import Compact.Completion.OtherCases.F4PointTransfers

/-! Further C972 deductions in the original twelve owners.  The missing
SE halfpoint is reduced to a genuine SE inward/east pair and an NE-owned
top origin.  The top marker remains absent; no top-wall square is introduced.
These are residual reductions, not an exclusion of the family. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem southeast_halfpoint_of_missing_g6 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside (113/50) 2) :
    (owners p 6).Inside 3 (3/2) := by
  have h := fixed p hf
  apply OrdinaryMarkerHalfpoint.point_original _ (43/500) (side p 6)
    (by norm_num) (by norm_num) h.southeastMarker h.southeastF8 (southeast_g8 p hf) missing
  · convert foreign p hf 6 11 (by decide) _ _ h.rightMarker using 1 <;> norm_num
  · exact foreign p hf 6 2 (by decide) _ _ h.southeastCorner
  · exact foreign p hf 6 10 (by decide) _ _ h.bottomG5

theorem southeast_g6_of_missing_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2)) :
    (owners p 6).Inside (113/50) 2 := by
  by_contra absent
  exact missing (southeast_halfpoint_of_missing_g6 p hf absent)

theorem southeast_east_of_g6 (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (g6 : (owners p 6).Inside (113/50) 2) :
    (owners p 6).Inside (5/2) 2 := by
  have h := fixed p hf
  exact F4PointTransfers.horizontal_original _ (side p 6) h.southeastMarker g6 h.southeastF8
    (foreign p hf 6 5 (by decide) _ _ h.southwestF4)
    (foreign p hf 6 10 (by decide) _ _ ((bottom_reach p hf).2 _ (by norm_num) (by norm_num)))

theorem northeast_origin_of_missing_southeast_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 6).Inside 3 (3/2)) :
    (owners p 7).Inside 2 3 := by
  by_contra absent
  exact missing (southeast_halfpoint_of_northeast_missing_origin p hf absent)

/-- If the SE halfpoint is available, the bottom missing-corner root
forces the true singleton 0 corner.  The other singleton then omits the
same corner, so the NW missing-F5 root is impossible. -/
theorem northwest_forward_of_southeast_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (half : (owners p 6).Inside 3 (3/2)) :
    (owners p 8).Inside 2 (113/50) := by
  have corner := zero_corner_of_southeast_halfpoint p hf half
  by_contra missing
  exact foreign p hf 1 0 (by decide) _ _ corner
    (one_corner_of_northwest_missing_f5 p hf missing)

/-- The remaining SE branch retains strict actual ownership of all three
points; the central NE square, rather than a fictitious top owner, owns
the top origin in this branch. -/
theorem southeast_alternative (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 3 (3/2) ∨
      ((owners p 6).Inside (113/50) 2 ∧ (owners p 6).Inside (5/2) 2 ∧
        (owners p 7).Inside 2 3) := by
  by_cases half : (owners p 6).Inside 3 (3/2)
  · exact Or.inl half
  · have g6 := southeast_g6_of_missing_halfpoint p hf half
    exact Or.inr ⟨g6,southeast_east_of_g6 p hf g6,
      northeast_origin_of_missing_southeast_halfpoint p hf half⟩

theorem northwest_missing_southeast_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 8).Inside 2 (113/50)) :
    (owners p 6).Inside (113/50) 2 ∧ (owners p 6).Inside (5/2) 2 ∧
      (owners p 7).Inside 2 3 := by
  exact (southeast_alternative p hf).resolve_left
    (fun half => missing (northwest_forward_of_southeast_halfpoint p hf half))

end
#print axioms southeast_alternative
#print axioms northwest_missing_southeast_points
end N12Compact.FiniteCases.C972
