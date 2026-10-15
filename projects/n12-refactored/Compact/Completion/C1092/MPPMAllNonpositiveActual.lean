import Compact.Completion.C1092.MPPMAllNonpositiveCycle
import Compact.Completion.C1092.MPPMActualNonpositiveCore
import Compact.Completion.C1092.MPPMActualCrosspoints
import Compact.Completion.C1092.MPPMMissingNegativeCentersActual

/-! Complete original-owner all-nonpositive ordinary ending. Each native
central frame keeps its own following actual bar; adjacent missing
owners compare the same actual wall center. The finite split concerns
only the four strict forward memberships. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
open C1092MPPMActualPositiveCycle C1092MPPMActualCrosspoints
set_option Elab.async false
noncomputable section

theorem actual_three_retaining_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s))
    (F : OpenSquare) (fframe : ActualFrame ((rotation 2).pullPacking p) F)
    (fn : Normal F.c (-F.s))
    (retainingC : Forward p) (retainingD : Forward ((rotation 1).pullPacking p))
    (retainingF : Forward ((rotation 2).pullPacking p)) : False := by
  let p' := (rotation 1).pullPacking p
  have family' := family_transport (rotation 1) p hf
  have context := rotation_context p hf hb 1
  have ordinary := Ordinary.rotated p hf h 1
  have c := C1092MPPMActualNonpositive.actual_core p hf hb h C frame cn retainingC
  have d := C1092MPPMActualNonpositive.actual_core p' family' context ordinary D dframe dn retainingD
  have f := C1092MPPMActualNonpositive.actual_core ((rotation 2).pullPacking p)
    (family_transport (rotation 2) p hf) (rotation_context p hf hb 2)
    (Ordinary.rotated p hf h 2) F fframe fn retainingF
  have ef := successor_frame p hf D dframe
  have ff := successor_frame p' family' F (rotated_frame p hf 1 1 F fframe)
  let B := (owners p 9).translated 2 2
  let R := (owners p' 9).translated 2 2
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have ractual (x y : ℝ) : R.Inside x y↔(owners p' 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p' 9) 2 2 x y
  apply three_retaining_impossible C D F B R c d f
    (frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm))
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  · exact fun x y both => owners_disjoint p' family' 4 5 (by decide) _ _
      ⟨(dframe.actual _ _).mp both.1,(ff.actual _ _).mp both.2⟩
  · intro x low high
    apply (bactual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p hf hb h C frame cn (2+x)
      (by linarith only [low]) (by linarith only [high])
  · exact fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bactual _ _).mp both.2⟩
  · intro x low high
    apply (ractual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p' family' context ordinary D dframe dn (2+x)
      (by linarith only [low]) (by linarith only [high])
  · exact fun x y both => owners_disjoint p' family' 4 9 (by decide) _ _
      ⟨(dframe.actual _ _).mp both.1,(ractual _ _).mp both.2⟩

theorem actual_alternating_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s))
    (F : OpenSquare) (fframe : ActualFrame ((rotation 3).pullPacking p) F)
    (fn : Normal F.c (-F.s))
    (retainingC : Forward p) (missingD : ¬Forward ((rotation 1).pullPacking p))
    (missingF : ¬Forward ((rotation 3).pullPacking p)) : False := by
  have c := C1092MPPMActualNonpositive.actual_core p hf hb h C frame cn retainingC
  have ds := C1092MPPMActualCentralOrigin.missing_strong_profile ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) missingD D dframe dn
  have fs := C1092MPPMActualCentralOrigin.missing_strong_profile ((rotation 3).pullPacking p)
    (family_transport (rotation 3) p hf) (rotation_context p hf hb 3)
    (Ordinary.rotated p hf h 3) missingF F fframe fn
  have sideD : 1<D.side := by
    rw [dframe.side]
    change 1<(((rotation 1).pullPacking p).square _).side
    rw [((rotation 1).pullPacking p).congruent]
    exact ((rotation 1).pullPacking p).side_gt_one
  have sideF : 1<F.side := by
    rw [fframe.side]
    change 1<(((rotation 3).pullPacking p).square _).side
    rw [((rotation 3).pullPacking p).congruent]
    exact ((rotation 3).pullPacking p).side_gt_one
  let E := C1092MMMPEndingAxes.clockwise D
  let W := counterclockwise F
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have wactual (x y : ℝ) : W.Inside x y↔(owners p 7).Inside (2+x) (2+y) := by
    rw [inside_counterclockwise,fframe.actual,owners_transport (rotation 3) p hf 4]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] <;> congr 1 <;> ring
  have wside : W.side=(owners p 7).side := by
    change F.side=(owners p 7).side
    rw [fframe.side,owners_transport (rotation 3) p hf 4]
    rfl
  let B := (owners p 9).translated 2 2
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  apply alternating_impossible C W E B c (missing_predecessor F sideF fn fs)
    (missing_successor D sideD dn ds)
    (frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans wside.symm))
    (frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm))
  · apply (wactual _ _).mpr
    norm_num
    simpa [marker] using (owners_markers p hf 7 11).mpr (by decide +kernel)
  · apply (ef.actual _ _).mpr
    norm_num
    simpa [marker] using (owners_markers p hf 5 9).mpr (by decide +kernel)
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.2
  · exact fun x y both => owners_disjoint p hf 4 7 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(wactual _ _).mp both.2⟩
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  · intro x low high
    apply (bactual _ _).mpr
    norm_num
    exact C1092MPPMActualNonpositive.bottom_bar p hf hb h C frame cn (2+x)
      (by linarith only [low]) (by linarith only [high])
  · exact fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bactual _ _).mp both.2⟩

/-- Every actual ordinary sector is nonpositive. All sixteen strict
forward membership patterns are excluded by the three actual geometric
alternatives above and the same-wall adjacent-missing contradiction. -/
theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) (C : Fin 4→OpenSquare)
    (frame : ∀ i,ActualFrame ((rotation i).pullPacking p) (C i))
    (normal : ∀ i,Normal (C i).c (-(C i).s)) : False := by
  let retains : Fin 4→Prop := fun i => Forward ((rotation i).pullPacking p)
  have one (i : Fin 4) : addSector i 1=i+1 := by fin_cases i <;> rfl
  have two (i : Fin 4) : addSector i 2=i+2 := by fin_cases i <;> rfl
  have three (i : Fin 4) : addSector i 3=i+3 := by fin_cases i <;> rfl
  apply binary_cycle retains
  · intro i current next
    let p' := (rotation i).pullPacking p
    have family' := family_transport (rotation i) p hf
    have context := rotation_context p hf hb i
    have ordinary := Ordinary.rotated p hf h i
    have next' : ¬Forward ((rotation 1).pullPacking p') := by
      intro own
      apply next
      have old := (forward_composed_iff p hf i 1).mpr own
      simpa only [retains,one i] using old
    exact C1092MPPMMissingNegativeCenters.adjacent_missing_impossible p' family' context ordinary
      (C i) (frame i) (normal i) (C (addSector i 1))
      (rotated_frame p hf i 1 _ (frame (addSector i 1))) (normal (addSector i 1))
      current (fun own => next' ((next_forward_iff p' family').mpr own))
  · intro i current next last
    exact actual_three_retaining_impossible ((rotation i).pullPacking p)
      (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
      (C i) (frame i) (normal i)
      (C (addSector i 1)) (rotated_frame p hf i 1 _ (frame (addSector i 1))) (normal (addSector i 1))
      (C (addSector i 2)) (rotated_frame p hf i 2 _ (frame (addSector i 2))) (normal (addSector i 2))
      current (forward_composed p hf i 1 (by simpa only [retains,one i] using next))
      (forward_composed p hf i 2 (by simpa only [retains,two i] using last))
  · intro i current next previous
    have missingNext : ¬Forward ((rotation 1).pullPacking ((rotation i).pullPacking p)) := by
      intro own
      apply next
      have old := (forward_composed_iff p hf i 1).mpr own
      simpa only [retains,one i] using old
    have missingPrevious : ¬Forward ((rotation 3).pullPacking ((rotation i).pullPacking p)) := by
      intro own
      apply previous
      have old := (forward_composed_iff p hf i 3).mpr own
      simpa only [retains,three i] using old
    exact actual_alternating_impossible ((rotation i).pullPacking p)
      (family_transport (rotation i) p hf) (rotation_context p hf hb i) (Ordinary.rotated p hf h i)
      (C i) (frame i) (normal i)
      (C (addSector i 1)) (rotated_frame p hf i 1 _ (frame (addSector i 1))) (normal (addSector i 1))
      (C (addSector i 3)) (rotated_frame p hf i 3 _ (frame (addSector i 3))) (normal (addSector i 3))
      current missingNext missingPrevious

end
#print axioms actual_three_retaining_impossible
#print axioms actual_alternating_impossible
#print axioms impossible
end N12Compact.C1092MPPMAllNonpositive
