import Compact.Completion.C1092.MPPMActualBoundaryOrigin
import Compact.Completion.C1092.MPPMPositiveCrosspointAngleDichotomy
import Compact.Completion.C1092.MPPMPositiveRetainingSteep

/-! Actual ordinary positive crosspoint seeds and the positive retaining
successor corollary. A recipient's own-sector chart and its common
physical chart refer to the same original Q5. No recipient angle ceiling
or support cap is assumed. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualRetaining
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C977CornerCubic C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMActualBoundaryOrigin C1092MPPMPositiveCrosspointAngleDichotomy
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

structure SuccessorFrame (p : NormalizedPacking) (E : OpenSquare) : Prop where
  side : E.side=(owners p 5).side
  actual : ∀ x y,E.Inside x y↔(owners p 5).Inside (2+x) (2+y)

/-- Sector addition concerns only the four simultaneous rigid motions;
it enumerates no square poses or auxiliary ownership components. -/
def addSector (i j : Fin 4) : Fin 4 := ⟨(i.val+j.val)%4,Nat.mod_lt _ (by decide)⟩

theorem identity_frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (C : OpenSquare) (frame : ActualFrame p C) :
    ActualFrame ((rotation 0).pullPacking p) C := by
  have same : owners ((rotation 0).pullPacking p) 4=owners p 4 := by
    rw [owners_transport (rotation 0) p hf 4]
    rfl
  constructor
  · rw [same]; exact frame.side
  · intro x y; rw [same]; exact frame.actual x y

theorem original_frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (C : OpenSquare) (frame : ActualFrame ((rotation 0).pullPacking p) C) :
    ActualFrame p C := by
  have same : owners ((rotation 0).pullPacking p) 4=owners p 4 := by
    rw [owners_transport (rotation 0) p hf 4]
    rfl
  constructor
  · rw [←same]; exact frame.side
  · intro x y; rw [←same]; exact frame.actual x y

/-- Composing two sector motions transports the same supplied physical
frame. Its cosine and sine are unchanged, including their zero endpoints. -/
theorem rotated_frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 4) (C : OpenSquare)
    (frame : ActualFrame ((rotation (addSector i j)).pullPacking p) C) :
    ActualFrame ((rotation j).pullPacking ((rotation i).pullPacking p)) C := by
  have family' := family_transport (rotation i) p hf
  constructor
  · rw [frame.side,owners_transport (rotation (addSector i j)) p hf 4,
      owners_transport (rotation j) ((rotation i).pullPacking p) family' 4,
      owners_transport (rotation i) p hf (ownerAction (rotation j) 4)]
    fin_cases i <;> fin_cases j <;> rfl
  · intro x y
    rw [frame.actual,owners_transport (rotation (addSector i j)) p hf 4,
      owners_transport (rotation j) ((rotation i).pullPacking p) family' 4,
      owners_transport (rotation i) p hf (ownerAction (rotation j) 4)]
    fin_cases i <;> fin_cases j <;>
      norm_num [addSector,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX,inside_pullY]

/-- Simultaneous quarter turn of the packing and its actual recipient.
The final common physical chart has not reflected either central alone. -/
theorem successor_frame (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (D : OpenSquare) (frame : ActualFrame ((rotation 1).pullPacking p) D) :
    SuccessorFrame p (C1092MMMPEndingAxes.clockwise D) := by
  constructor
  · change D.side=(owners p 5).side
    rw [frame.side,owners_transport (rotation 1) p hf 4]
    rfl
  · intro x y
    rw [C1092MMMPEndingAxes.inside_clockwise,frame.actual,
      owners_transport (rotation 1) p hf 4]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    rw [show (4:ℝ)-(2+-x)=2+x by ring]

/-- A positive retaining central has its strict actual crosspoint at
every canonical angle, using the universal preceding-origin exclusion. -/
theorem forward_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s) :
    (owners p 4).Inside (3/2) 2 :=
  C1092MPPMPositiveSeedsActual.forward_crosspoint p hf
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    h.southwest.1 h.southwest.2 forward
    (positive_previous_excluded p hf hb h C frame cn sp)
    (far_points p hf hb h).2.1 C frame cn

/-- The successor's own forward point and the next actual Q6 crosspoint
give the full shallow alternative. The steep alternative contradicts
the completed two-square retaining theorem with the actual positive Q4.
No membership of the successor's omitted backward point is reassigned. -/
theorem retaining_successor_shallow (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c D.s) (tp : 0<D.s)
    (forward : (owners p 5).Inside 2 (87/50))
    (next : (owners p 6).Inside (5/2) 2) : Shallow D := by
  let g := rotation 1
  let p' := g.pullPacking p
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 1
  have ordinary := Ordinary.rotated p hf h 1
  have forward' : (owners p' 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact forward
  have previous := positive_previous_excluded p' family' context ordinary D dframe dn tp
  have core := forward_core p' family'
    (C1092MPPMActualWallReduction.bottom_ordinary p' family' context)
    ordinary.southwest.1 ordinary.southwest.2 forward' previous D dframe
  have input := forward_inputs p' family'
    (C1092MPPMActualWallReduction.bottom_ordinary p' family' context)
    ordinary.southwest.1 ordinary.southwest.2 forward' previous
    (far_points p' family' context ordinary).2.1 D dframe
  let E := C1092MMMPEndingAxes.clockwise D
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have nextMissing : ¬D.Inside 0 (-1/2) := by
    intro own
    have original := (ef.actual _ _).mp
      ((C1092MMMPEndingAxes.inside_clockwise D (1/2) 0).mpr
        (by simpa only [neg_div] using own))
    norm_num at original
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨original,next⟩
  rcases classify D (by rw [dframe.side]; exact side_gt p' 4) dn tp core
      input.northMarker nextMissing with shallow|steep
  · exact shallow
  · have current := positive_faces p hf hb h C frame cn sp
    have recipient := positive_faces p' family' context ordinary D dframe dn tp
    have side : 1<C.side := by rw [frame.side]; exact side_gt p 4
    have same : C.side=E.side := frame.side.trans ((side_same p 4 5).trans ef.side.symm)
    have markerC : C.Inside (-7/20) (-7/20) := by
      apply (frame.actual _ _).mpr
      norm_num
      simpa [marker] using mark p hf 4 8 (by decide +kernel)
    have markerE : E.Inside (7/20) (-7/20) := by
      dsimp only [E]
      rw [C1092MMMPEndingAxes.inside_clockwise]
      norm_num
      simpa only [neg_div] using core.marker
    have raw : C1092MPPMPositiveRetainingSteep.Input C E := by
      refine { side := side
               same := same
               central := cn
               recipient := dn
               lowerA := ?_
               upperA := current.2
               upperK := current.1.upperV
               nearAE := ?_
               positiveKE := ?_
               upperKE := ?_
               lowerK := ?_
               capAE := recipient.2
               steep := (steep_sine dn steep.angle).le
               lowKE := ?_
               markerC := markerC
               markerE := markerE
               apart := ?_ }
      · linarith only [current.1.lowerU]
      · change -(13/50)*D.c<D.loU+D.side
        linarith only [core.forward.2.1]
      · change 0< -(-D.loV-D.side)
        linarith only [core.forward.2.2.2,dn.1]
      · change -(-D.loV-D.side)≤D.s
        linarith only [recipient.1.upperV]
      · linarith only [current.1.lowerV]
      · change C.side-D.c/2≤-(-D.loV-D.side)
        change C.side=D.side at same
        linarith only [steep.lowerV,same]
      · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
          ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
    exact False.elim (C1092MPPMPositiveRetainingSteep.impossible C E raw)

/-- The same retaining corollary in the original Q4 sector. Its actual
predecessor is Q7, represented in the inverse-quarter-turn packing; the
recipient and next crosspoint remain actual Q4 and Q5 respectively. -/
theorem retaining_shallow (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c W.s) (wp : 0<W.s)
    (forward : (owners p 4).Inside (87/50) 2)
    (next : (owners p 5).Inside 2 (3/2)) : Shallow C := by
  let g := rotation 3
  have family' := family_transport g p hf
  have target : ActualFrame ((rotation 1).pullPacking (g.pullPacking p)) C := by
    apply rotated_frame p hf 3 1 C
    change ActualFrame ((rotation 0).pullPacking p) C
    exact identity_frame p hf C frame
  have forward' : (owners (g.pullPacking p) 5).Inside 2 (87/50) := by
    rw [owners_transport g p hf 5]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact forward
  have next' : (owners (g.pullPacking p) 6).Inside (5/2) 2 := by
    rw [owners_transport g p hf 6]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact next
  exact retaining_successor_shallow (g.pullPacking p) family'
    (rotation_context p hf hb 3) (Ordinary.rotated p hf h 3)
    W wframe wn wp C target cn sp forward' next'

theorem retaining_halfpoint_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (sp : 0<C.s)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c W.s) (wp : 0<W.s)
    (forward : (owners p 4).Inside (87/50) 2)
    (next : (owners p 5).Inside 2 (3/2)) :
    Shallow C ∧ (owners p 4).Inside 1 (3/2) ∧ (owners p 9).Inside 2 1 := by
  have small := retaining_shallow p hf hb h C frame cn sp W wframe wn wp forward next
  have half : (owners p 4).Inside 1 (3/2) := by
    have original := (frame.actual _ _).mp small.outer
    norm_num at original
    exact original
  exact ⟨small,half,bottom_origin_of_halfpoint p hf
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb) half⟩

end
#print axioms forward_crosspoint
#print axioms retaining_successor_shallow
#print axioms retaining_shallow
#print axioms retaining_halfpoint_origin
end N12Compact.C1092MPPMActualRetaining
