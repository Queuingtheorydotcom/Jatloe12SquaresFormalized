import Compact.Completion.C1092.MPPMActualAllPositive
import Compact.Completion.C1092.MPPMNegativeCrosspointComplete
import Compact.Completion.C1092.MPPMMissingNegativeCrosspointComplete

/-! Universal positive crosspoints in the actual ordinary four-cycle.
One canonical frame is retained for each actual owner. A nonpositive
successor supplies a terminal transfer for either forward membership;
a positive successor propagates its actual crosspoint backwards. Both
successor-sign scalar joins are supplied by the complete source modules.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualCrosspoints
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
open C1092MPPMActualPositiveCycle
set_option Elab.async false
noncomputable section

/-- Literal forward ownership under composition of two simultaneous
sector turns. The whole interior of one actual owner is transported. -/
theorem forward_composed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 4) (point : Forward ((rotation (addSector i j)).pullPacking p)) :
    Forward ((rotation j).pullPacking ((rotation i).pullPacking p)) := by
  let C := (owners ((rotation (addSector i j)).pullPacking p) 4).translated 2 2
  have old : ActualFrame ((rotation (addSector i j)).pullPacking p) C :=
    ⟨rfl,fun x y => inside_translated_iff _ 2 2 x y⟩
  have frame := rotated_frame p hf i j C old
  have own : C.Inside (-13/50) 0 := by
    apply (old.actual _ _).mpr
    norm_num
    exact point
  have original := (frame.actual _ _).mp own
  norm_num at original
  exact original

theorem next_forward_iff (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Forward ((rotation 1).pullPacking p)↔(owners p 5).Inside 2 (87/50) := by
  change (owners ((rotation 1).pullPacking p) 4).Inside (87/50) 2↔_
  rw [owners_transport (rotation 1) p hf 4]
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX]

theorem forward_composed_iff (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i j : Fin 4) : Forward ((rotation (addSector i j)).pullPacking p)↔
      Forward ((rotation j).pullPacking ((rotation i).pullPacking p)) := by
  constructor
  · exact forward_composed p hf i j
  · intro own
    let C := (owners ((rotation (addSector i j)).pullPacking p) 4).translated 2 2
    have old : ActualFrame ((rotation (addSector i j)).pullPacking p) C :=
      ⟨rfl,fun x y => inside_translated_iff _ 2 2 x y⟩
    have frame := rotated_frame p hf i j C old
    have point : C.Inside (-13/50) 0 := by
      apply (frame.actual _ _).mpr; norm_num; exact own
    have original := (old.actual _ _).mp point
    norm_num at original
    exact original

/-- Every actual successor sign is included. A positive successor is
asked only for its own crosspoint; a nonpositive one needs no such point.
Forward omission is always an omission from its indicated owner. -/
theorem positive_crosspoint_of_successor
    (scalar : C1092MPPMMissingNegativeCrosspointGeometry.ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (canonical : |D.s|≤D.c)
    (next : 0<D.s→(owners p 5).Inside 2 (3/2)) : (owners p 4).Inside (3/2) 2 := by
  by_cases forward : (owners p 4).Inside (87/50) 2
  · exact C1092MPPMActualRetaining.forward_crosspoint p hf hb h forward C frame cn positive
  · by_cases successor : 0<D.s
    · have dn : Normal D.c D.s :=
        ⟨successor.le,(abs_le.mp canonical).2,D.unit_normal⟩
      exact positive_propagation_of_scalars C1092MPPMActualPositiveCycle.scalar_proof
        p hf hb h forward C frame cn positive D dframe dn successor (next successor)
    · have nonpositive := le_of_not_gt successor
      have dn : Normal D.c (-D.s) :=
        ⟨by linarith only [nonpositive],by linarith only [(abs_le.mp canonical).1],
          by nlinarith only [D.unit_normal]⟩
      by_cases retaining : (owners p 5).Inside 2 (87/50)
      · exact C1092MPPMNegativeCrosspointGeometry.crosspoint
          p hf hb h forward C frame cn positive D dframe dn retaining
      · exact C1092MPPMMissingNegativeCrosspointGeometry.crosspoint_of_scalars scalar
          p hf hb h forward C frame cn positive D dframe dn retaining

private theorem backward_cycle (P : Fin 4→Prop) (seed : ∃ i,P i)
    (step : ∀ i,P (addSector i 1)→P i) : ∀ i,P i := by
  obtain ⟨i,own⟩ := seed
  have first : P (addSector i 3) := step _ (by
    convert own using 1 <;> fin_cases i <;> rfl)
  have second : P (addSector i 2) := step _ (by
    convert first using 1 <;> fin_cases i <;> rfl)
  have third : P (addSector i 1) := step _ (by
    convert second using 1 <;> fin_cases i <;> rfl)
  intro j
  fin_cases i <;> fin_cases j <;>
    first | exact own | exact first | exact second | exact third

/-- The positive crosspoint conclusion for every fixed actual sector
frame, including mixed signs and all sixteen forward memberships. The
finite step concerns four rigid sector indices, never square poses. -/
theorem positive_crosspoints_of_scalars
    (scalar : C1092MPPMMissingNegativeCrosspointGeometry.ScalarProof)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : Fin 4→OpenSquare)
    (frame : ∀ i,ActualFrame ((rotation i).pullPacking p) (C i))
    (canonical : ∀ i,|(C i).s|≤(C i).c) :
    ∀ i,0<(C i).s→Crosspoint ((rotation i).pullPacking p) := by
  classical
  by_cases all : ∀ i,0<(C i).s
  · have positive : PositiveFrames p := fun i =>
      ⟨C i,frame i,⟨(all i).le,(abs_le.mp (canonical i)).2,(C i).unit_normal⟩,all i⟩
    have points := C1092MPPMActualPositiveCycle.all_crosspoints p hf hb h positive
    exact fun i _ => points i
  · let P : Fin 4→Prop := fun i => 0<(C i).s→Crosspoint ((rotation i).pullPacking p)
    have seed : ∃ i,P i := by
      obtain ⟨i,nonpositive⟩ := not_forall.mp all
      exact ⟨i,fun positive => False.elim (nonpositive positive)⟩
    apply backward_cycle P seed
    intro i next positive
    let p' := (rotation i).pullPacking p
    have family' := family_transport (rotation i) p hf
    have context := rotation_context p hf hb i
    have ordinary := Ordinary.rotated p hf h i
    have cn : Normal (C i).c (C i).s :=
      ⟨positive.le,(abs_le.mp (canonical i)).2,(C i).unit_normal⟩
    apply positive_crosspoint_of_successor scalar p' family' context ordinary
      (C i) (frame i) cn positive (C (addSector i 1))
      (rotated_frame p hf i 1 _ (frame (addSector i 1))) (canonical (addSector i 1))
    intro successor
    exact next_crosspoint p' family'
      (crosspoint_composed p hf i 1 (next successor))

theorem positive_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (canonical : |D.s|≤D.c)
    (next : 0<D.s→(owners p 5).Inside 2 (3/2)) : (owners p 4).Inside (3/2) 2 :=
  positive_crosspoint_of_successor C1092MPPMMissingNegativeCrosspointGeometry.scalar_proof
    p hf hb h C frame cn positive D dframe canonical next

/-- All continuous scalar dependencies in the signed four-cycle are
proved. The sole frame inputs identify the four actual central owners. -/
theorem positive_crosspoints (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : Fin 4→OpenSquare)
    (frame : ∀ i,ActualFrame ((rotation i).pullPacking p) (C i))
    (canonical : ∀ i,|(C i).s|≤(C i).c) :
    ∀ i,0<(C i).s→Crosspoint ((rotation i).pullPacking p) :=
  positive_crosspoints_of_scalars C1092MPPMMissingNegativeCrosspointGeometry.scalar_proof
    p hf hb h C frame canonical

/-- The retaining nonpositive crosspoint is an elementary strict-band
consequence of its own ordinary outer point and its own forward point.
It needs no claimed owner of any omitted auxiliary. -/
theorem nonpositive_retaining_crosspoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2) : (owners p 4).Inside (3/2) 2 := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have G : C.Inside (-1) (-2/5) := by
    apply (frame.actual _ _).mpr; norm_num; exact h.southwest.2
  have T : C.Inside (-13/50) 0 := by
    apply (frame.actual _ _).mpr; norm_num; exact forward
  have point : C.Inside (-1/2) 0 := by
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [G.1,T.2.1,G.2.2.1,T.2.2.2,cp,cn.1,cn.2.1]
  have original := (frame.actual _ _).mp point
  norm_num at original
  exact original

theorem retaining_crosspoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (canonical : |C.s|≤C.c)
    (forward : (owners p 4).Inside (87/50) 2) : (owners p 4).Inside (3/2) 2 := by
  by_cases positive : 0<C.s
  · exact C1092MPPMActualRetaining.forward_crosspoint p hf hb h forward C frame
      ⟨positive.le,(abs_le.mp canonical).2,C.unit_normal⟩ positive
  · exact nonpositive_retaining_crosspoint p hf hb h C frame
      ⟨by linarith only [le_of_not_gt positive],by linarith only [(abs_le.mp canonical).1],
        by nlinarith only [C.unit_normal]⟩ forward

end
#print axioms positive_crosspoint_of_successor
#print axioms positive_crosspoints_of_scalars
#print axioms positive_crosspoints
#print axioms retaining_crosspoint
end N12Compact.C1092MPPMActualCrosspoints
