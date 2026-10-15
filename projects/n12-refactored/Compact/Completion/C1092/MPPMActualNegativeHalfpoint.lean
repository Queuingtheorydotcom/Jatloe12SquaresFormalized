import Compact.Completion.C1092.MPPMActualPositiveOrder
import Compact.Completion.C1092.MPPMForwardPositiveDActual
import Compact.Completion.C1092.MPPMNonpositivePredecessor

/-! ORDINARY-NEGATIVE-HALFPOINT Corollary 2 on the original MPPM owners.
The source of each missing-forward raw point is supplied before the
two-square theorem is used. Its source may have either canonical sign.
The target's own forward omission is handled by the all-angle ordinary
halfpoint theorem, with a simultaneous whole-packing turn.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualNegativeHalfpoint
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMActualPositiveOrder C1092MPPMForwardPositiveD
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

theorem southeast_of_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (missing : ¬(owners p 5).Inside 2 (87/50)) :
    (owners p 5).Inside (5/2) 1 := by
  let g := rotation 1
  have family' := family_transport g p hf
  have context := rotation_context p hf hb 1
  have P : (owners (g.pullPacking p) 4).Inside 1 (87/50) := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact h.southeast.2
  have G : (owners (g.pullPacking p) 4).Inside 1 (8/5) := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact h.southeast.1
  have absent : ¬(owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact missing
  have point := C1092MPPMPositiveSeedsActual.missing_halfpoint
    (g.pullPacking p) family' context P G absent
  rw [owners_transport g p hf 4] at point
  norm_num [g,rotation,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at point
  exact point

theorem southeast (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (J : OpenSquare) (frameJ : OwnerFrame p 5 J)
    (ep : 0<J.c) (en : J.s≤0) (eo : -J.s≤J.c) :
    (owners p 5).Inside (5/2) 1 := by
  by_cases forward : (owners p 5).Inside 2 (87/50)
  · obtain ⟨C,frameC,cp,co⟩ := C1092MPPMPositiveSeedsActual.exists_canonical_frame p
    let E := J.translated 2 2
    have actualE (x y : ℝ) : E.Inside x y↔(owners p 5).Inside (2+x) (2+y) := by
      have translated := inside_translated_iff J 2 2 x y
      exact translated.trans (frameJ.actual _ _)
    have M : (owners p 4).Inside (33/20) (33/20) := by
      simpa [marker] using mark p hf 4 8 (by decide +kernel)
    have N : (owners p 7).Inside (33/20) (47/20) := by
      simpa [marker] using mark p hf 7 11 (by decide +kernel)
    have W : (owners p 8).Inside (457/500) 2 := by
      simpa [marker] using mark p hf 8 12 (by decide +kernel)
    have K : (owners p 0).Inside 1 1 := by
      simpa [cornerOwner,cornerPoint] using corner_points p hf 0
    have ME : (owners p 5).Inside (47/20) (33/20) := by
      simpa [marker] using mark p hf 5 9 (by decide +kernel)
    have inputs : C1092MPPMNonpositivePredecessor.Inputs C E := by
      refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · apply (frameC.actual _ _).mpr; norm_num; exact M
      · apply (frameC.actual _ _).mpr; norm_num; exact h.southwest.1
      · apply (frameC.actual _ _).mpr; norm_num; exact h.southwest.2
      · intro own
        have original := (frameC.actual _ _).mp own
        norm_num at original
        exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨original,K⟩
      · intro own
        have original := (frameC.actual _ _).mp own
        norm_num at original
        exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨original,W⟩
      · intro own
        have original := (frameC.actual _ _).mp own
        norm_num at original
        exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨original,N⟩
      · intro own
        have original := (frameC.actual _ _).mp own
        norm_num at original
        exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨original,(wall_auxiliaries p hb).1⟩
      · intro missing
        have absent : ¬(owners p 4).Inside (87/50) 2 := by
          intro own
          apply missing
          apply (frameC.actual _ _).mpr
          norm_num
          exact own
        exact C1092MPPMPositiveSeedsActual.missing_inputs p hf hb
          h.southwest.1 h.southwest.2 absent (far_points p hf hb h).2.1 C frameC
      · apply (actualE _ _).mpr; norm_num; exact ME
      · apply (actualE _ _).mpr; norm_num; exact h.southeast.2
      · apply (actualE _ _).mpr; norm_num; exact h.southeast.1
      · apply (actualE _ _).mpr; norm_num; exact forward
      · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
          ⟨(frameC.actual _ _).mp both.1,(actualE _ _).mp both.2⟩
    have point := C1092MPPMNonpositivePredecessor.point C E
      (by rw [frameC.side]; exact side_gt p 4)
      (frameC.side.trans ((side_same p 4 5).trans frameJ.side.symm))
      cp co ep en eo inputs
    have original := (actualE _ _).mp point
    norm_num at original
    exact original
  · exact southeast_of_missing p hf hb h forward

/-- Full original Q4 halfpoint producer required by the earlier positive
D theorem. The frame given by that interface is transported, rather than
replaced by a newly chosen angle or a pose from another packing. -/
theorem southwest (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (F : OpenSquare) (frame : OwnerFrame p 4 F)
    (cp : 0<F.c) (range : |F.s|≤F.c) (nonpositive : F.s≤0) :
    (owners p 4).Inside 1 (3/2) := by
  let g := rotation 3
  let J := turnFrame (turnFrame (turnFrame (g.pull F)))
  have owner : owners (g.pullPacking p) 5=g.pull (owners p 4) := by
    rw [owners_transport g p hf 5]
    rfl
  have frameJ : OwnerFrame (g.pullPacking p) 5 J := by
    constructor
    · rw [owner]
      simpa only [J,turnFrame_side,pull_same_side] using frame.side
    · intro x y
      rw [owner]
      simp only [J,turnFrame_inside,inside_pull]
      exact frame.actual _ _
  have jp : 0<J.c := by
    dsimp [J,g,rotation,turnFrame,Transform.pull,pullSwap,pullY]
    linarith only [cp]
  have jn : J.s≤0 := by
    dsimp [J,g,rotation,turnFrame,Transform.pull,pullSwap,pullY]
    linarith only [nonpositive]
  have jo : -J.s≤J.c := by
    dsimp [J,g,rotation,turnFrame,Transform.pull,pullSwap,pullY]
    linarith only [(abs_le.mp range).1]
  have point := southeast (g.pullPacking p) (family_transport g p hf)
    (rotation_context p hf hb 3) (Ordinary.rotated p hf h 3) J frameJ jp jn jo
  rw [owner] at point
  norm_num [g,rotation,Transform.pull,inside_pullSwap,inside_pullY] at point
  exact point

theorem nonpositive_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p) : NonpositiveHalfpoint p := by
  intro C frame cp range nonpositive
  exact southwest p hf hb h C frame cp range nonpositive

theorem bottom_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : Ordinary p)
    (F : OpenSquare) (frame : OwnerFrame p 4 F)
    (cp : 0<F.c) (range : |F.s|≤F.c) (nonpositive : F.s≤0) :
    (owners p 9).Inside 2 1 :=
  C1092MPPMPositiveSeedsActual.bottom_origin_of_halfpoint p hf
    (C1092MPPMActualWallReduction.bottom_ordinary p hf hb)
    (southwest p hf hb h F frame cp range nonpositive)

/-- The actual remaining premise of FORWARD-OWNED-POSITIVE-D is now
filled by the ordinary nonpositive halfpoint theorem above. -/
theorem southeast_positive_previous_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (forward : (owners p 5).Inside 2 (87/50))
    (J : OpenSquare) (frame : OwnerFrame p 5 J) (cp : 0<J.c) (sn : 0≤J.s) :
    ¬(owners p 5).Inside 2 1 :=
  southeast_of_nonpositive_halfpoint p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb)
    h.southwest.1 h.southwest.2 forward J frame cp sn
    (nonpositive_halfpoint p hf hb h)

theorem southwest_positive_previous_excluded (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm) (h : Ordinary p)
    (forward : (owners p 4).Inside (87/50) 2)
    (F : OpenSquare) (frame : OwnerFrame p 4 F) (cp : 0<F.c) (sn : 0≤F.s) :
    ¬(owners p 4).Inside 1 2 := by
  let g := rotation 3
  let J := turnFrame (turnFrame (turnFrame (g.pull F)))
  have owner : owners (g.pullPacking p) 5=g.pull (owners p 4) := by
    rw [owners_transport g p hf 5]
    rfl
  have frameJ : OwnerFrame (g.pullPacking p) 5 J := by
    constructor
    · rw [owner]
      simpa only [J,turnFrame_side,pull_same_side] using frame.side
    · intro x y
      rw [owner]
      simp only [J,turnFrame_inside,inside_pull]
      exact frame.actual _ _
  have jp : 0<J.c := by
    dsimp [J,g,rotation,turnFrame,Transform.pull,pullSwap,pullY]
    linarith only [cp]
  have jn : 0≤J.s := by
    dsimp [J,g,rotation,turnFrame,Transform.pull,pullSwap,pullY]
    linarith only [sn]
  have forwardJ : (owners (g.pullPacking p) 5).Inside 2 (87/50) := by
    rw [owner]
    norm_num [g,rotation,Transform.pull,inside_pullSwap,inside_pullY]
    exact forward
  have absent := southeast_positive_previous_excluded (g.pullPacking p)
    (family_transport g p hf) (rotation_context p hf hb 3) (Ordinary.rotated p hf h 3)
    forwardJ J frameJ jp jn
  rw [owner] at absent
  norm_num [g,rotation,Transform.pull,inside_pullSwap,inside_pullY] at absent
  exact absent

end
#print axioms southeast
#print axioms nonpositive_halfpoint
#print axioms bottom_origin
#print axioms southwest_positive_previous_excluded
end N12Compact.C1092MPPMActualNegativeHalfpoint
