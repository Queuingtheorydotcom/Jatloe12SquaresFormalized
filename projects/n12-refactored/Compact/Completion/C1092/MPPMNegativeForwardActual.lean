import Compact.Completion.C1092.MPPMNegativeForward
import Compact.Completion.C1092.MPPMActualCentralOrigin

/-! Literal Corollary 3 of NEGATIVE-FORWARD-POSITIVE-H. The negative
retaining source is the actual Q4, the recipient is the actual Q5, and
both endpoints of the foreign bar belong to the same actual Q9. The
recipient's canonical sign and its own forward omission are exhaustive
alternatives. No backward-inner exclusion is assumed. Source only,
uncompiled. -/
namespace N12Compact.C1092MPPMNegativeForwardActual
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual
open C1092MPPMForwardPositiveD
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

/-- The source's unconditional nonpositive halfpoint supplies Q9's
origin. Convexity then fills the entire closed interval from its genuine
ordinary far point to that origin, including both endpoints. -/
theorem bottom_segment (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (x : ℝ) (low : 36/25≤x) (high : x≤2) : (owners p 9).Inside x 1 := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have sn : C.s≤0 := by linarith only [cn.1]
  have range : |C.s|≤C.c := by rw [abs_of_nonpos sn]; exact cn.2.1
  have origin := C1092MPPMActualNegativeHalfpoint.bottom_origin p hf hb ordinary
    (C.translated (-2) (-2)) (C1092MPPMPositiveOverlap.owner_frame p C frame)
    cp range sn
  let k := (25/14)*(x-36/25)
  have kn : 0≤k := by dsimp only [k]; nlinarith only [low]
  have ku : k≤1 := by dsimp only [k]; nlinarith only [high]
  have point := inside_segment (owners p 9) (36/25) 1 2 1 k
    (far_points p hf hb ordinary).2.1 origin kn ku
  convert point using 1 <;> dsimp only [k] <;> ring

private theorem positive_retaining_successor (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (ordinary : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (J : OpenSquare) (frameJ : OwnerFrame p 5 J) (jn : Normal J.c J.s)
    (nextForward : (owners p 5).Inside 2 (87/50)) :
    (owners p 5).Inside (5/2) 1 := by
  let E := J.translated 2 2
  let B := (owners p 9).translated 2 2
  have actualE (x y : ℝ) : E.Inside x y↔(owners p 5).Inside (2+x) (2+y) :=
    (inside_translated_iff J 2 2 x y).trans (frameJ.actual _ _)
  have actualB (x y : ℝ) : B.Inside x y↔(owners p 9).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 9) 2 2 x y
  have previous := C1092MPPMActualCentralOrigin.nonpositive_retaining_excluded
    p hf hb ordinary C frame cn forward
  have input : C1092MPPMNegativeForward.Input C E B := by
    refine { side := ?_, same := ?_, sourceNormal := cn, targetNormal := jn,
      source := ?_, ordinary := ?_, outer := ?_, forward := ?_,
      previous := ?_, northwest := ?_, target := ?_, bar0 := ?_, bar1 := ?_,
      inner := ?_, wholeBar := ?_, apart := ?_, apartBar := ?_ }
    · rw [frame.side]; exact side_gt p 4
    · exact frame.side.trans ((side_same p 4 5).trans frameJ.side.symm)
    · apply (frame.actual _ _).mpr
      norm_num
      simpa [marker] using mark p hf 4 8 (by decide +kernel)
    · apply (frame.actual _ _).mpr; norm_num; exact ordinary.southwest.1
    · apply (frame.actual _ _).mpr; norm_num; exact ordinary.southwest.2
    · apply (frame.actual _ _).mpr; norm_num; exact forward
    · intro own
      apply previous
      have original := (frame.actual _ _).mp own
      norm_num at original
      exact original
    · intro own
      have original := (frame.actual _ _).mp own
      norm_num at original
      have foreign : (owners p 7).Inside (33/20) (47/20) := by
        simpa [marker] using mark p hf 7 11 (by decide +kernel)
      exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨original,foreign⟩
    · apply (actualE _ _).mpr
      norm_num
      simpa [marker] using mark p hf 5 9 (by decide +kernel)
    · apply (actualE _ _).mpr; norm_num; exact ordinary.southeast.2
    · apply (actualE _ _).mpr; norm_num; exact ordinary.southeast.1
    · apply (actualE _ _).mpr; norm_num; exact nextForward
    · intro x low high
      apply (actualB _ _).mpr
      norm_num
      exact bottom_segment p hf hb ordinary C frame cn (2+x)
        (by linarith only [low]) (by linarith only [high])
    · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
        ⟨(frame.actual _ _).mp both.1,(actualE _ _).mp both.2⟩
    · exact fun x y both => owners_disjoint p hf 4 9 (by decide) _ _
        ⟨(frame.actual _ _).mp both.1,(actualB _ _).mp both.2⟩
  have original := (actualE _ _).mp (C1092MPPMNegativeForward.point C E B input)
  norm_num at original
  exact original

/-- Every canonical recipient sign is retained. A missing recipient
forward point invokes the separate all-angle halfpoint theorem; the
remaining branch uses the same physical Q5 in the raw two-square proof. -/
theorem successor_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2) : (owners p 5).Inside (5/2) 1 := by
  obtain ⟨J,frameJ,jp,range⟩ := exists_owner_frame p 5
  by_cases positive : 0<J.s
  · by_cases nextForward : (owners p 5).Inside 2 (87/50)
    · have jn : Normal J.c J.s :=
        ⟨positive.le,by simpa only [abs_of_pos positive] using range,J.unit_normal⟩
      exact positive_retaining_successor p hf hb ordinary C frame cn forward J frameJ jn nextForward
    · exact C1092MPPMActualNegativeHalfpoint.southeast_of_missing p hf hb ordinary nextForward
  · exact C1092MPPMActualNegativeHalfpoint.southeast p hf hb ordinary J frameJ jp
      (le_of_not_gt positive) (by simpa only [abs_of_nonpos (le_of_not_gt positive)] using range)

/-- The genuine paired-corner transfer is applied after the strict Q5
halfpoint is proved. The entire packing is turned, preserving Q1, Q10,
their real walls, their common side and their actual strict anchors. -/
theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (ordinary : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2) : (owners p 10).Inside 3 2 := by
  have half := successor_halfpoint p hf hb ordinary C frame cn forward
  let g := rotation 1
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 1
  have half' : (owners (g.pullPacking p) 4).Inside 1 (3/2) := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact half
  have point := bottom_origin_of_halfpoint (g.pullPacking p) family'
    (C1092MPPMActualWallReduction.bottom_ordinary (g.pullPacking p) family' context) half'
  rw [owners_transport g p hf 9] at point
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at point
  exact point

end
#print axioms bottom_segment
#print axioms successor_halfpoint
#print axioms right_origin
end N12Compact.C1092MPPMNegativeForwardActual
