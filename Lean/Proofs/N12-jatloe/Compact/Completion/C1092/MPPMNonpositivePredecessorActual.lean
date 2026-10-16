import Compact.Completion.C1092.MPPMAllNonpositiveShallow
import Compact.Completion.C1092.MPPMActualNonpositiveCore

/-! Literal missing-negative predecessor application of the narrow
retaining profile. The stronger missing profile has its preceding-D
exclusion proved upstream; the actual Q9 bar is produced from C's own
nonpositive halfpoint and the unconditional ordinary far advance.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMAllNonpositive
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem narrow_of_missing_predecessor (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 3).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (missing : ¬(owners p 7).Inside 2 (113/50)) : Shallow C := by
  let g := rotation 3
  let p' := g.pullPacking p
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 3
  have ordinary := Ordinary.rotated p hf h 3
  have missing' : ¬(owners p' 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact missing
  have strong := C1092MPPMActualCentralOrigin.missing_strong_profile
    p' family' context ordinary missing' D dframe dn
  have sideD : 1<D.side := by
    rw [dframe.side]
    change 1<(p'.square _).side
    rw [p'.congruent]
    exact p'.side_gt_one
  let W := counterclockwise D
  have wactual (x y : ℝ) : W.Inside x y↔(owners p 7).Inside (2+x) (2+y) := by
    rw [inside_counterclockwise,dframe.actual,owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] <;> congr 1 <;> ring
  have wside : W.side=(owners p 7).side := by
    change D.side=(owners p 7).side
    rw [dframe.side,owners_transport g p hf 4]
    rfl
  have profile : MissingPredecessor W := missing_predecessor D sideD dn strong
  have marker : W.Inside (-7/20) (7/20) := by
    apply (wactual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  let B := (owners p 9).translated 2 2
  have bactual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  exact predecessor_shallow C W B
    (C1092MPPMActualNonpositive.actual_core p hf hb h C frame cn forward) profile
    (frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans wside.symm)) marker
    (fun x y both => owners_disjoint p hf 4 7 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(wactual _ _).mp both.2⟩)
    (by
      intro x low high
      apply (bactual _ _).mpr
      norm_num
      exact C1092MPPMActualNonpositive.bottom_bar p hf hb h C frame cn (2+x)
        (by linarith only [low]) (by linarith only [high]))
    (fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(bactual _ _).mp both.2⟩)

end
#print axioms narrow_of_missing_predecessor
end N12Compact.C1092MPPMAllNonpositive
