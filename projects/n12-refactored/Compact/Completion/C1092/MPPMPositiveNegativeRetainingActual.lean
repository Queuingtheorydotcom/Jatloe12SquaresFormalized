import Compact.Completion.C1092.MPPMPositiveNegativeRetaining
import Compact.Completion.C1092.MPPMActualNonpositiveCore

/-! Literal Corollary 2 of POSITIVE-NEGATIVE-RETAINING-SHALLOW.
The successor's ordinary faces, origin and entire right bar are produced
from its actual nonpositive frame. The next strict crosspoint remains
in its separately named actual central owner. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMPositiveNegativeRetaining
open S12 S12Pilot C977CornerCubic
open C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMPositiveSeedsActual C1092MPPMActualRetaining
set_option Elab.async false
noncomputable section

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

/-- Every point of the whole actual Q10 segment has that one owner.
Its strict origin is supplied by Q5's own nonpositive halfpoint. -/
theorem actual_right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (D : OpenSquare) (frame : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (y : ℝ) (low : -(14/25)≤y) (high : y≤0) :
    (owners p 10).Inside 3 (2+y) := by
  have origin := C1092MPPMActualNonpositive.bottom_origin ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) D frame dn
  rw [owners_transport (rotation 1) p hf 9] at origin
  norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at origin
  exact CommonCases.OriginalOwners.vertical_segment (owners p 10) 3 (36/25) 2 (2+y)
    (far_points p hf hb h).2.2.1 origin (by norm_num)
    (by linarith only [low]) (by linarith only [high])

theorem actual_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (forward : (owners p 5).Inside 2 (87/50))
    (next : (owners p 6).Inside (5/2) 2) :
    Input C (C1092MMMPEndingAxes.clockwise D) ((owners p 10).translated 2 2) := by
  let E := C1092MMMPEndingAxes.clockwise D
  let R := (owners p 10).translated 2 2
  have ef : SuccessorFrame p E := successor_frame p hf D dframe
  have ractual (x y : ℝ) : R.Inside x y↔(owners p 10).Inside (2+x) (2+y) :=
    inside_translated_iff (owners p 10) 2 2 x y
  have forward' : (owners ((rotation 1).pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport (rotation 1) p hf 4]
    norm_num [rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact forward
  have core := C1092MPPMActualNonpositive.actual_core ((rotation 1).pullPacking p)
    (family_transport (rotation 1) p hf) (rotation_context p hf hb 1)
    (Ordinary.rotated p hf h 1) D dframe dn forward'
  have faces := C1092MPPMActualBoundaryOrigin.positive_faces p hf hb h C frame cn positive
  refine ⟨?_,frame.side.trans (((p.congruent _).trans (p.congruent _).symm).trans ef.side.symm),
    cn,dn,?_,faces.1.lowerU,faces.1.upperV,?_,?_,?_,?_,
    C1092MPPMAllNonpositive.successor_faces D core,?_,?_,?_,?_⟩
  · rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  · apply (frame.actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  · apply (ef.actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.2
  · apply (ef.actual _ _).mpr; norm_num; exact h.southeast.1
  · apply (ef.actual _ _).mpr; norm_num; exact forward
  · intro own
    have original := (ef.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨original,next⟩
  · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(ef.actual _ _).mp both.2⟩
  · exact fun x y both => owners_disjoint p hf 5 10 (by decide) _ _
      ⟨(ef.actual _ _).mp both.1,(ractual _ _).mp both.2⟩
  · intro y low high
    apply (ractual _ _).mpr
    norm_num
    exact actual_right_bar p hf hb h D dframe dn y low high

theorem actual_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (forward : (owners p 5).Inside 2 (87/50))
    (next : (owners p 6).Inside (5/2) 2) : Profile (C1092MMMPEndingAxes.clockwise D) :=
  profile C (C1092MMMPEndingAxes.clockwise D) ((owners p 10).translated 2 2)
    (actual_input p hf hb h C frame cn positive D dframe dn forward next)

/-- Native-face form used by the local one/two/three-positive endings. -/
theorem actual_native (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c C.s) (positive : 0<C.s)
    (D : OpenSquare) (dframe : ActualFrame ((rotation 1).pullPacking p) D)
    (dn : Normal D.c (-D.s)) (forward : (owners p 5).Inside 2 (87/50))
    (next : (owners p 6).Inside (5/2) 2) :
    97/100<D.c ∧ 4*(-D.s)<D.c ∧ D.loV+D.side<43/500 := by
  have result := actual_profile p hf hb h C frame cn positive D dframe dn forward next
  have dp : 0<D.c := by linarith only [(normal_bounds dn).1]
  have slope := (div_lt_iff₀ dp).mp result.slope
  have height := result.height
  change -(-D.loV-D.side)<43/500 at height
  exact ⟨result.cosine,by linarith only [slope],by linarith only [height]⟩

/-- The representative negative Q4 after a positive actual predecessor.
All twelve owners and the next crosspoint undergo the same quarter turn. -/
theorem narrow_of_positive_predecessor (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (C : OpenSquare) (frame : ActualFrame p C) (cn : Normal C.c (-C.s))
    (forward : (owners p 4).Inside (87/50) 2)
    (W : OpenSquare) (wframe : ActualFrame ((rotation 3).pullPacking p) W)
    (wn : Normal W.c W.s) (positive : 0<W.s)
    (next : (owners p 5).Inside 2 (3/2)) :
    97/100<C.c ∧ 4*(-C.s)<C.c ∧ C.loV+C.side<43/500 := by
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
  exact actual_native (g.pullPacking p) family' (rotation_context p hf hb 3)
    (Ordinary.rotated p hf h 3) W wframe wn positive C target cn forward' next'

end
#print axioms actual_input
#print axioms actual_native
#print axioms narrow_of_positive_predecessor
end N12Compact.C1092MPPMPositiveNegativeRetaining
