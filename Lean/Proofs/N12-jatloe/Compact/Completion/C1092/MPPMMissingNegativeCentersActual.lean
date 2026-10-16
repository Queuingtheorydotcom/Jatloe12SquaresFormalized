import Compact.Completion.C1092.MPPMMissingNegativeCenters
import Compact.Completion.C1092.MPPMActualCentralOriginMissing

/-! The literal original-owner application of the missing-negative
center inequalities. The strong profile uses the now-produced preceding
origin exclusion. For consecutive missing sectors the one required strict
boundary origin follows from the first sector's own omission. -/
namespace N12Compact.C1092MPPMMissingNegativeCenters
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance C1092MPPMActualPositiveOrder
open C1092MPPMPositiveSeedsActual
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

theorem actual_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) : Data C := by
  have core := C1092MPPMMissingNegativeProfile.actual_core p hf hb ordinary missing C frame
  exact ⟨cn,core.marker,core.ordinaryP,
    C1092MPPMActualCentralOrigin.missing_strong_profile p hf hb ordinary missing C frame cn⟩

theorem actual_bottom_order (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) :
    9/5<centerX (owners p 9) := by
  let B := (owners p 9).translated 2 2
  have actual (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) := by
    simpa only [add_comm] using inside_translated_iff (owners p 9) 2 2 x y
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  have result := bottom_order C B (by rw [frame.side]; exact side_gt p 4)
    (frame.side.trans (side_same p 4 9)) (actual_data p hf hb ordinary missing C frame cn)
    (by apply (actual _ _).mpr; norm_num; exact bm)
    (by apply (actual _ _).mpr; norm_num; exact C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((actual _ _).mp own)).2.2.1
      linarith only [wall])
    (fun x y own => owners_disjoint p hf 4 9 (by decide) _ _
      ⟨(frame.actual _ _).mp own.1,(actual _ _).mp own.2⟩)
  have center : centerX B=centerX (owners p 9)-2 := center_translate_x _ _ _
  rw [center] at result
  linarith only [result]

theorem actual_left_order (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (leftOrigin : (owners p 8).Inside 1 2)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s)) :
    11/5<centerY (owners p 8) := by
  let L := (owners p 8).translated 2 2
  have actual (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) := by
    simpa only [add_comm] using inside_translated_iff (owners p 8) 2 2 x y
  have lm : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have result := left_order C L (by rw [frame.side]; exact side_gt p 4)
    (frame.side.trans (side_same p 4 8)) (actual_data p hf hb ordinary missing C frame cn)
    (by apply (actual _ _).mpr; norm_num; exact lm)
    (by apply (actual _ _).mpr; norm_num; exact leftOrigin)
    (by
      intro x y own
      have wall := (p.contained _ _ _ ((actual _ _).mp own)).1
      linarith only [wall])
    (fun x y own => owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(frame.actual _ _).mp own.1,(actual _ _).mp own.2⟩)
  have center : centerY L=centerY (owners p 8)-2 := center_translate_y _ _ _
  rw [center] at result
  linarith only [result]

/-- Two consecutive nonpositive missing-forward central owners are
impossible. The middle boundary is the same original Q9 in both proofs. -/
theorem adjacent_missing_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (ordinary : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (D : OpenSquare) (nextFrame : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s))
    (missingC : ¬(owners p 4).Inside (87/50) 2)
    (missingD : ¬(owners p 5).Inside 2 (87/50)) : False := by
  have first := actual_bottom_order p hf hb ordinary missingC C frame cn
  let g := rotation 1
  have family' := family_transport g p hf
  have context' := rotation_context p hf hb 1
  have ordinary' := Ordinary.rotated p hf ordinary 1
  have missing' : ¬(owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact missingD
  have originalOrigin : (owners p 9).Inside 2 1 :=
    bottom_origin_of_missing p hf hb
      (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
      ordinary.southwest.1 ordinary.southwest.2 missingC
  have origin' : (owners (g.pullPacking p) 8).Inside 1 2 := by
    rw [owners_transport g p hf 8]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact originalOrigin
  have last := actual_left_order (g.pullPacking p) family' context' ordinary'
    missing' origin' D nextFrame dn
  rw [owners_transport g p hf 8] at last
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    center_pullSwap_x,center_pullSwap_y,center_pullX_x,center_pullX_y] at last
  linarith only [first,last]

end
#print axioms actual_bottom_order
#print axioms actual_left_order
#print axioms adjacent_missing_impossible
end N12Compact.C1092MPPMMissingNegativeCenters
