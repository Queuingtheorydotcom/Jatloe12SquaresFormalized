import Compact.Completion.C1092.MPPMPositiveOverlapLocal
import Compact.Completion.C1092.MPPMActualNegativeHalfpoint

/-! Literal original Q4 application of CENTERED-POSITIVE-OVERLAP. The
positive-forward D theorem supplies its actual preceding-origin absence.
The actual Q5 halfpoint, and hence actual Q10 origin, precede its angle
deduction. All transformed points retain their physical owners.
This source is uncompiled. -/
namespace N12Compact.C1092MPPMPositiveOverlap
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C977CornerCubic
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- Undo only the coordinate translation, preserving this exact frame. -/
theorem owner_frame (p : NormalizedPacking) (C : OpenSquare) (frame : ActualFrame p C) :
    C1092MPPMForwardPositiveD.OwnerFrame p 4 (C.translated (-2) (-2)) := by
  constructor
  · exact frame.side
  · intro x y
    rw [inside_translated_iff,frame.actual]
    rw [show (2:ℝ)+(-2+x)=x by ring,show (2:ℝ)+(-2+y)=y by ring]

theorem previous_absent (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    ¬(owners p 4).Inside 1 2 :=
  C1092MPPMActualNegativeHalfpoint.southwest_positive_previous_excluded p hf hb ordinary
    forward (C.translated (-2) (-2)) (owner_frame p C frame)
    (by change 0<C.c; linarith only [(normal_bounds cn).1]) cn.1

/-- The source's backward point is the actual next square's omitted
forward point. The all-angle ordinary halfpoint and paired-corner theorem
then put the origin in that next wall, with no angle premise on Q5. -/
theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (backward : (owners p 4).Inside 2 (87/50)) : (owners p 10).Inside 3 2 := by
  let g := rotation 1
  have hf' := family_transport g p hf
  have hb' := rotation_context p hf hb 1
  have ordinary' := Ordinary.rotated p hf ordinary 1
  have missing : ¬(owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact fun own => owners_disjoint p hf 5 4 (by decide) _ _ ⟨own,backward⟩
  have point := C1092MPPMPositiveSeedsActual.bottom_origin_of_missing
    (g.pullPacking p) hf' hb'
    (C1092MPPMActualWallReduction.bottom_ordinary (g.pullPacking p) hf' hb')
    ordinary'.southwest.1 ordinary'.southwest.2 missing
  rw [owners_transport g p hf 9] at point
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at point
  exact point

theorem original_center_absent (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (backward : (owners p 4).Inside 2 (87/50))
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) :
    ¬(owners p 4).Inside 2 2 := by
  let Q := (owners p 5).translated 2 2
  obtain ⟨E,ep,canonical,shape,equiv,_⟩ := ClosedFrames.canonical_frame Q
  have eActual (x y : ℝ) : E.Inside x y↔(owners p 5).Inside (2+x) (2+y) :=
    (equiv x y).trans (inside_translated_iff (owners p 5) 2 2 x y)
  have same : C.side=E.side := frame.side.trans ((side_same p 4 5).trans shape.symm)
  have walls := C1092MPPMActualWallReduction.wall_pairs p hf hb
  have far := (far_points p hf hb ordinary).2.1
  have previous := previous_absent p hf hb ordinary forward C frame cn
  have core := forward_inputs p hf walls.2.1.1 ordinary.southwest.1 ordinary.southwest.2
    forward previous far C frame
  have ME : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  have B : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  have K : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have short : (owners p 10).Inside 3 (161/100) := by
    have point := inside_segment (owners p 10) 3 (8/5) 3 (87/50) (1/14)
      walls.2.2.1.2 walls.2.2.1.1 (by norm_num) (by norm_num)
    norm_num at point
    exact point
  have originR := right_origin p hf hb ordinary backward
  have h : Inputs C E := by
    refine ⟨core,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · apply (frame.actual _ _).mpr; norm_num; exact backward
    · apply (eActual _ _).mpr; norm_num; exact ME
    · apply (eActual _ _).mpr; norm_num; exact ordinary.southeast.2
    · apply (eActual _ _).mpr; norm_num; exact ordinary.southeast.1
    · intro own
      have original := (eActual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨original,short⟩
    · intro own
      have original := (eActual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨original,B⟩
    · intro own
      have original := (eActual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨original,K⟩
    · intro own
      have original := (eActual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨original,originR⟩
    · intro own
      have original := (eActual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨original,walls.2.2.1.2⟩
    · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
        ⟨(frame.actual _ _).mp both.1,(eActual _ _).mp both.2⟩
  intro own
  apply center_absent C E (by rw [frame.side]; exact side_gt p 4) same cn ep canonical h
  apply (frame.actual _ _).mpr
  norm_num
  exact own

end
#print axioms original_center_absent
end N12Compact.C1092MPPMPositiveOverlap
