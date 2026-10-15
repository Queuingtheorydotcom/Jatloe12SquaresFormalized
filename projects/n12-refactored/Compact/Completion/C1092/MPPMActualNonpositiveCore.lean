import Compact.Completion.C1092.MPPMAllNonpositiveCore
import Compact.Completion.C1092.MPPMActualCentralOriginMissing
import Compact.Completion.C1092.MPPMNegativeForwardActual

/-! Shared literal actual entrance for the remaining nonpositive
ordinary comparisons. The strict halfpoint, preceding-origin omission,
corner, marker and full following-wall segment are all genuine original
sources. No sign or membership of a different central is assumed.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualNonpositive
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
set_option Elab.async false
noncomputable section

theorem halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) :
    (owners p 4).Inside 1 (3/2) := by
  have canonical : |C.s|≤C.c := by
    rw [abs_of_nonpos (show C.s≤0 by linarith only [cn.1])]
    exact cn.2.1
  exact C1092MPPMActualNegativeHalfpoint.southwest p hf hb h (C.translated (-2) (-2))
    (C1092MPPMPositiveOverlap.owner_frame p C frame)
    (by linarith only [(normal_bounds cn).1]) canonical (by linarith only [cn.1])

theorem bottom_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) :
    (owners p 9).Inside 2 1 :=
  bottom_origin_of_halfpoint p hf (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    (halfpoint p hf hb h C frame cn)

theorem bottom_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (x : ℝ) (low : 36/25≤x) (high : x≤2) : (owners p 9).Inside x 1 :=
  C1092MPPMNegativeForwardActual.bottom_segment p hf hb h C frame cn x low high

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem actual_core (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2) : C1092MPPMAllNonpositive.Core C := by
  have canonical : |C.s|≤C.c := by
    rw [abs_of_nonpos (show C.s≤0 by linarith only [cn.1])]
    exact cn.2.1
  have half := halfpoint p hf hb h C frame cn
  have previous := C1092MPPMActualCentralOrigin.previous_excluded p hf hb h C frame canonical
  refine ⟨?_,cn,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  · apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.2
  · apply (frame.actual _ _).mpr; norm_num; exact forward
  · apply (frame.actual _ _).mpr; norm_num; exact half
  · intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    exact previous original
  · intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    have corner : (owners p 0).Inside 1 1 := by
      simpa [cornerOwner,cornerPoint] using corner_points p hf 0
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨original,corner⟩
  · intro own
    have original := (frame.actual _ _).mp own
    norm_num at original
    have foreign : (owners p 7).Inside (33/20) (47/20) := by
      simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
    exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨original,foreign⟩

end
#print axioms actual_core
#print axioms bottom_bar
end N12Compact.C1092MPPMActualNonpositive
