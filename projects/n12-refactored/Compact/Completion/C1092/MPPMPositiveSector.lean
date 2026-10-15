import Compact.Completion.C1092.MPPMPositiveSeedsActual
import Compact.Completion.C1092.MPPMOrdinaryWallAdvance

/-! Preferred original-owner joins for the positive ordinary MPPM sector.
The far bottom point is now produced from the ordinary actual successor
and the no-omission wall entrance. The halfpoint, wall origin, four faces
and strict angle entrance are consequently simultaneous conclusions.

Remaining completed-source producers are kept distinct: the universal
retaining-sector preceding-origin exclusion (FORWARD-OWNED-POSITIVE-D,
Theorem 1), the small missing-forward ceiling when used, and the final
missing-positive boundary envelopes/order. This module proves no whole
BranchEnding0 and makes no compiler-acceptance claim. -/
namespace N12Compact.C1092MPPMPositiveSector
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MPPMEntrance C1092MPPMOmissions C1092MPPMPositiveSeedsActual
open C977CornerCubic
set_option Elab.async false

/-- Missing-forward ordinary Q4 supplies its actual halfpoint and Q9
origin, plus all four same-square positive faces and the strict angle
bound. There is no additional far-point or support hypothesis. -/
theorem missing_points_and_faces (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (successor : (owners p 5).Inside (113/50) 1)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    (owners p 4).Inside 1 (3/2) ∧ (owners p 9).Inside 2 1 ∧
      C1092MPPMMissingPositiveFaces.Faces C := by
  have walls := ordinary_walls p hb empty
  have far := C1092MPPMOrdinaryWallAdvance.bottom_far_no_omission p hf hb empty successor
  exact ⟨missing_halfpoint p hf hb P G missing,
    bottom_origin_of_missing p hf hb walls.2.1.1 P G missing,
    missing_profile p hf hb P G missing far C frame cn⟩

theorem missing_crosspoint_of_ceiling (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (successor : (owners p 5).Inside (113/50) 1)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s)
    (small : C1092WallProfileScalars.half C.c C.s≤1/3) :
    (owners p 4).Inside (3/2) 2 :=
  missing_crosspoint p hf hb P G missing
    (C1092MPPMOrdinaryWallAdvance.bottom_far_no_omission p hf hb empty successor)
    C frame cn small

/-- The far-point producer is also available in the retained-forward
alternative. The preceding origin remains only a literal exclusion from
Q4 until its completed two-square producer has been transcribed. -/
theorem forward_crosspoint_of_previous_exclusion (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (successor : (owners p 5).Inside (113/50) 1)
    (forward : (owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    (owners p 4).Inside (3/2) 2 := by
  have walls := ordinary_walls p hb empty
  exact forward_crosspoint p hf walls.2.1.1 P G forward previous
    (C1092MPPMOrdinaryWallAdvance.bottom_far_no_omission p hf hb empty successor)
    C frame cn

/-- The two genuine next-owner alternatives can supply their strict
crosspoint independently. Once it is strict in actual Q5, the cap,
backward omission, Q4 halfpoint and Q9 origin follow together. -/
theorem retaining_points_of_next_crosspoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (next : (owners p 5).Inside 2 (3/2))
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s)
    (positive : 0<C.s) (small : C1092WallProfileScalars.half C.c C.s≤1/3) :
    C.loU+C.side≤-C.s/2 ∧ ¬(owners p 4).Inside 2 (87/50) ∧
      (owners p 4).Inside 1 (3/2) ∧ (owners p 9).Inside 2 1 := by
  have walls := ordinary_walls p hb empty
  exact forward_halfpoint_and_origin p hf walls.2.1.1 P G forward previous next
    C frame cn positive small

#print axioms missing_points_and_faces
#print axioms missing_crosspoint_of_ceiling
#print axioms forward_crosspoint_of_previous_exclusion
end N12Compact.C1092MPPMPositiveSector
