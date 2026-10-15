import Compact.Completion.C1092.MPPMEntrance
import Compact.Completion.C1092.MPPMPositiveCrosspointSeeds
import Compact.Completion.C1092.MMMP.MarkerHalfpoint
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! Literal original-owner applications of the MPPM ordinary halfpoint,
positive missing-forward profile, and positive crosspoint seeds.
The marker/corner/wall points retain owners 0,4,7,8,9 throughout.
The Q9 far point and, in the forward-owned alternative, the exclusion of
the preceding origin remain explicit named point obligations. Their
completed prose producers are NONORDINARY-ISOLATION section 5 and
FORWARD-OWNED-POSITIVE-D Theorem 1; those producers are not replaced by
assumed face inequalities here. Source-only, without compiler acceptance. -/
namespace N12Compact.C1092MPPMPositiveSeedsActual
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic
set_option Elab.async false

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

/-- A canonical reindexing of this same original square in the translated
chart. The structure makes no assumption about a point or a face. -/
structure ActualFrame (p : NormalizedPacking) (C : OpenSquare) : Prop where
  side : C.side=(owners p 4).side
  actual : ∀ x y, C.Inside x y ↔ (owners p 4).Inside (2+x) (2+y)

theorem exists_canonical_frame (p : NormalizedPacking) :
    ∃ C : OpenSquare, ActualFrame p C ∧ 0<C.c ∧ |C.s|≤C.c := by
  let Q := (owners p 4).translated 2 2
  obtain ⟨C,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame Q
  refine ⟨C,⟨shape,?_⟩,cp,range⟩
  intro x y
  have exactChart := (inside x y).trans (inside_translated_iff (owners p 4) 2 2 x y)
  simpa only [add_comm] using exactChart

/-- The missing-forward ordinary halfpoint uses no central sign,
preceding origin or far-wall advance. All four exclusions come from
their literal owners or from the central's stated own omission. -/
theorem missing_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (missing : ¬(owners p 4).Inside (87/50) 2) :
    (owners p 4).Inside 1 (3/2) := by
  let Q := (pullX (owners p 4)).translated 2 2
  have actual (x y : ℝ) : Q.Inside x y ↔ (owners p 4).Inside (2-x) (2+y) := by
    simp only [Q,inside_translated_iff,inside_pullX]
    rw [show 4-(2+x)=2-x by ring]
  have markC : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have markL : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  have bottomG := (wall_auxiliaries p hb).2.1
  have point := C1092MMMPMarkerHalfpoint.point Q (43/500)
    (by norm_num) (by norm_num) (side_gt p 4)
    (by apply (actual _ _).mpr; norm_num; exact markC)
    (by apply (actual _ _).mpr; norm_num; exact P)
    (by apply (actual _ _).mpr; norm_num; exact G)
    (by intro own; have h := (actual _ _).mp own; norm_num at h; exact missing h)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨h,markL⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨h,corner⟩)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,bottomG⟩)
  have result := (actual _ _).mp point
  norm_num at result
  exact result

/-- The strict halfpoint is foreign to actual corner Q0. Its full
all-angle support theorem then supplies the actual bottom-wall origin.
The only ordinary-wall point premise needed here is strict F2 in Q9. -/
theorem bottom_origin_of_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (half : (owners p 4).Inside 1 (3/2)) :
    (owners p 9).Inside 2 1 := by
  have markB : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have markK : (owners p 0).Inside 1 (457/500) := by
    simpa [marker] using marker_point p hf 0 0 (by decide +kernel)
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  exact Completion.OtherCases.WallProfile.boundary_origin
    (owners p 9) (owners p 0) (457/500) (8/5)
    (side_gt p 9) (side_same p 9 0)
    (fun x y own => (p.contained _ _ _ own).2.2.1)
    (fun x y own => ⟨(p.contained _ _ _ own).1,(p.contained _ _ _ own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    markB bottomF markK corner
    (fun own => owners_disjoint p hf 0 4 (by decide) _ _ ⟨own,half⟩)
    (fun x y own => owners_disjoint p hf 0 9 (by decide) x y own)

theorem bottom_origin_of_missing (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (missing : ¬(owners p 4).Inside (87/50) 2) :
    (owners p 9).Inside 2 1 :=
  bottom_origin_of_halfpoint p hf bottomF (missing_halfpoint p hf hb P G missing)

/-- Exact geometric inputs for the positive missing-forward face
producer. The one far point remains strict in its named actual Q9. -/
theorem missing_inputs (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (far : (owners p 9).Inside (36/25) 1)
    (C : OpenSquare) (frame : ActualFrame p C) :
    C1092MPPMMissingPositiveFaces.Inputs C := by
  have half := missing_halfpoint p hf hb P G missing
  have markC : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have markK : (owners p 0).Inside (457/500) 1 := by
    simpa [marker] using marker_point p hf 0 1 (by decide +kernel)
  have markL : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  have bottomG := (wall_auxiliaries p hb).2.1
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply (frame.actual _ _).mpr; norm_num; exact markC
  · apply (frame.actual _ _).mpr; norm_num; exact P
  · apply (frame.actual _ _).mpr; norm_num; exact G
  · apply (frame.actual _ _).mpr; norm_num; exact half
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨h,corner⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨h,markK⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨h,markL⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact missing h
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,far⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,bottomG⟩

theorem missing_profile (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (far : (owners p 9).Inside (36/25) 1)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    C1092MPPMMissingPositiveFaces.Faces C :=
  C1092MPPMMissingPositiveFaces.profile C (by rw [frame.side]; exact side_gt p 4) cn
    (missing_inputs p hf hb P G missing far C frame)

/-- A strict point in the original Q4, under the exact remaining
half-angle ceiling. No owner is invented for its omitted forward point. -/
theorem missing_crosspoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (far : (owners p 9).Inside (36/25) 1)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s)
    (small : C1092WallProfileScalars.half C.c C.s≤1/3) :
    (owners p 4).Inside (3/2) 2 := by
  have point := C1092MPPMPositiveCrosspointSeeds.crosspoint_of_missing C
    (by rw [frame.side]; exact side_gt p 4) cn
    (missing_inputs p hf hb P G missing far C frame) small
  have result := (frame.actual _ _).mp point
  norm_num at result
  exact result

theorem forward_core (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) :
    C1092MPPMPositiveCrosspointSeeds.ForwardCore C := by
  have markC : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · apply (frame.actual _ _).mpr; norm_num; exact markC
  · apply (frame.actual _ _).mpr; norm_num; exact P
  · apply (frame.actual _ _).mpr; norm_num; exact G
  · apply (frame.actual _ _).mpr; norm_num; exact forward
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨h,corner⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact previous h
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,bottomF⟩

/-- The retained-forward point ledger. The preceding-origin premise is
only its genuine exclusion from the actual central owner; no alternate
owner is supplied or assumed for that point. -/
theorem forward_inputs (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (far : (owners p 9).Inside (36/25) 1)
    (C : OpenSquare) (frame : ActualFrame p C) :
    C1092MPPMPositiveCrosspointSeeds.ForwardInputs C := by
  have core := forward_core p hf bottomF P G forward previous C frame
  have markN : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  refine ⟨core.marker,core.ordinaryP,core.ordinaryG,core.forward,
    core.corner,core.previousOrigin,core.bottom,?_,?_⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 9 (by decide) _ _ ⟨h,far⟩
  · intro own
    have h := (frame.actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨h,markN⟩

theorem forward_crosspoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (far : (owners p 9).Inside (36/25) 1)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    (owners p 4).Inside (3/2) 2 := by
  have point := C1092MPPMPositiveCrosspointSeeds.crosspoint_of_forward C
    (by rw [frame.side]; exact side_gt p 4) cn
    (forward_inputs p hf bottomF P G forward previous far C frame)
  have result := (frame.actual _ _).mp point
  norm_num at result
  exact result

/-- The foreign next crosspoint remains strict in actual Q5. The cap
and backward omission belong to this same actual Q4 frame, while the
outer halfpoint and its resulting origin belong to actual Q4 and Q9. -/
theorem forward_halfpoint_and_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (previous : ¬(owners p 4).Inside 1 2)
    (next : (owners p 5).Inside 2 (3/2))
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s)
    (positive : 0<C.s) (small : C1092WallProfileScalars.half C.c C.s≤1/3) :
    C.loU+C.side≤-C.s/2 ∧ ¬(owners p 4).Inside 2 (87/50) ∧
      (owners p 4).Inside 1 (3/2) ∧ (owners p 9).Inside 2 1 := by
  have markN : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have result := C1092MPPMPositiveCrosspointSeeds.halfpoint_of_next_crosspoint C
    (by rw [frame.side]; exact side_gt p 4) cn positive
    (forward_core p hf bottomF P G forward previous C frame)
    (by
      intro own
      have h := (frame.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨h,markN⟩)
    small
    (by
      intro own
      have h := (frame.actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 4 5 (by decide) _ _ ⟨h,next⟩)
  have half : (owners p 4).Inside 1 (3/2) := by
    have h := (frame.actual _ _).mp result.2.2
    norm_num at h
    exact h
  refine ⟨result.1,?_,half,bottom_origin_of_halfpoint p hf bottomF half⟩
  intro own
  apply result.2.1
  apply (frame.actual _ _).mpr
  norm_num
  exact own

#print axioms missing_halfpoint
#print axioms bottom_origin_of_missing
#print axioms missing_profile
#print axioms missing_crosspoint
#print axioms forward_crosspoint
#print axioms forward_halfpoint_and_origin
end N12Compact.C1092MPPMPositiveSeedsActual
