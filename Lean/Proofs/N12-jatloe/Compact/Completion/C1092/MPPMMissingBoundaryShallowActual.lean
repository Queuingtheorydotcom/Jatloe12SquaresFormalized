import Compact.Completion.C1092.MPPMMissingBoundaryShallow
import Compact.Completion.C1092.MPPMEntrance

/-! Literal original Q4/Q9 map for MISSING-BOUNDARY-SHALLOW-ANGLE,
section 7. Every strict/omitted point, real wall, side and disjointness
premise is obtained from these same two physical owners. The upstream
positive-C profile and negative-B sign are kept explicitly separate:
their completed producer is POSITIVE-BOUNDARY-ORIGIN, sections 6--7.
This adapter does not assert that those still-untranslated conclusions
follow from an arbitrary missing origin. Source-only. -/
namespace N12Compact.C1092MPPMMissingBoundaryShallow
open S12 S12Pilot C977CornerCubic C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
set_option Elab.async false
noncomputable section

/-- Face reindexings of the same original squares in one common chart. -/
structure ActualFrames (p : NormalizedPacking) (C B : OpenSquare) : Prop where
  centralSide : C.side=(owners p 4).side
  boundarySide : B.side=(owners p 9).side
  central : ∀ x y,C.Inside x y↔(owners p 4).Inside (2+x) (2+y)
  boundary : ∀ x y,B.Inside x y↔(owners p 9).Inside (2+x) (2+y)

/-- These are precisely the upstream conclusions of the completed
positive-boundary-origin chapter, not additional wall or support caps
introduced into the shallow local theorem. -/
structure CentralProfile (C : OpenSquare) : Prop where
  normal : Normal C.c C.s
  positive : 0<C.s
  lowerU : -C.c-C.s/2≤C.loU
  upperU : C.loU+C.side≤0
  upperV : C.loV+C.side≤C.s

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem actual_inputs (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 9).Inside 2 1)
    (C B : OpenSquare) (frames : ActualFrames p C B)
    (central : CentralProfile C)
    (normal : Normal B.c (-B.s)) (negative : 0< -B.s) : Input C B := by
  have markB : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have markK : (owners p 0).Inside 1 (457/500) := by
    simpa [marker] using marker_point p hf 0 0 (by decide +kernel)
  refine ⟨?_,?_,central.normal,central.positive,normal,negative,
    ?_,?_,central.lowerU,central.upperU,central.upperV,?_,?_,?_,?_,?_,?_⟩
  · rw [frames.centralSide]
    exact side_gt p 4
  · rw [frames.centralSide,frames.boundarySide]
    exact side_same p 4 9
  · apply (frames.central _ _).mpr; norm_num; exact G
  · apply (frames.central _ _).mpr; norm_num; exact forward
  · apply (frames.boundary _ _).mpr; norm_num; exact markB
  · apply (frames.boundary _ _).mpr; norm_num
    exact (wall_auxiliaries p hb).2.1
  · intro own
    have point := (frames.boundary _ _).mp own
    norm_num at point
    exact missing point
  · intro own
    have point := (frames.boundary _ _).mp own
    norm_num at point
    exact owners_disjoint p hf 9 0 (by decide) _ _ ⟨point,markK⟩
  · intro x y own
    have point := (frames.boundary x y).mp own
    have floor := (p.contained _ _ _ point).2.2.1
    linarith only [floor]
  · intro x y own
    exact owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frames.central _ _).mp own.1,(frames.boundary _ _).mp own.2⟩

/-- The original negative Q9's strict positive slope magnitude and
strict quarter ceiling, once its exact preceding profile is produced. -/
theorem actual_shallow (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 9).Inside 2 1)
    (C B : OpenSquare) (frames : ActualFrames p C B)
    (central : CentralProfile C)
    (normal : Normal B.c (-B.s)) (negative : 0< -B.s) :
    0<(-B.s)/B.c ∧ (-B.s)/B.c<1/4 := by
  have bp : 0<B.c := by linarith only [(strict_bounds normal negative).1]
  exact ⟨div_pos negative bp,shallow C B
    (actual_inputs p hf hb G forward missing C B frames central normal negative)⟩

end
#print axioms actual_inputs
#print axioms actual_shallow
end N12Compact.C1092MPPMMissingBoundaryShallow
