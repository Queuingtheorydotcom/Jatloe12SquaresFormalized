import Compact.Completion.C1092.MPPMForwardPositiveDLocal
import Compact.Completion.C1092.MPPMPositiveSeedsActual
import Compact.Completion.C1092.MPPMOmissions

/-! Actual-owner part of FORWARD-OWNED-POSITIVE-D Theorem 1.
The paired-corner contraposition is proved here, including the real walls
and strict original Q0/Q9 anchors. The positive Q4-to-Q5 branch is complete.
The final sign-unrestricted predecessor join names its remaining producer
`NonpositiveHalfpoint`: the ordinary negative halfpoint Corollary 2, whose
other predecessor-sign branches are translated separately. This is an
explicit conditional join, not an unconditional OOOO theorem. No boundary
origin ownership or desired central-origin exclusion is an input.
Source-only; no compiler acceptance is claimed. -/
namespace N12Compact.C1092MPPMForwardPositiveD
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMOmissions
set_option Elab.async false

/-- A frame reindexing of one literal original square, without a change
of physical coordinates or a point/support assumption. -/
structure OwnerFrame (p : NormalizedPacking) (i : Fin 12) (C : OpenSquare) : Prop where
  side : C.side=(owners p i).side
  actual : ∀ x y,C.Inside x y ↔ (owners p i).Inside x y

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) :
    1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  exact (p.congruent _).trans (p.congruent _).symm

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem exists_owner_frame (p : NormalizedPacking) (i : Fin 12) :
    ∃ C : OpenSquare,OwnerFrame p i C ∧ 0<C.c ∧ |C.s|≤C.c := by
  obtain ⟨C,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame (owners p i)
  exact ⟨C,⟨shape,inside⟩,cp,range⟩

/-- Contraposition of the full actual paired-corner theorem. If Q9 omits
its origin, the halfpoint is strictly in Q0. In particular, it is not
assigned to Q0 merely because it is absent from another owner. -/
theorem corner_halfpoint_of_missing_bottom_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (missing : ¬(owners p 9).Inside 2 1) :
    (owners p 0).Inside 1 (3/2) := by
  classical
  by_contra half
  have markB : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_point p hf 9 13 (by decide +kernel)
  have markK : (owners p 0).Inside 1 (457/500) := by
    simpa [marker] using marker_point p hf 0 0 (by decide +kernel)
  have corner : (owners p 0).Inside 1 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 0
  apply missing
  exact Completion.OtherCases.WallProfile.boundary_origin
    (owners p 9) (owners p 0) (457/500) (8/5)
    (side_gt p 9) (side_same p 9 0)
    (fun x y own => (p.contained _ _ _ own).2.2.1)
    (fun x y own => ⟨(p.contained _ _ _ own).1,(p.contained _ _ _ own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    markB bottomF markK corner half
    (fun x y own => owners_disjoint p hf 0 9 (by decide) x y own)

/-- All predecessor omissions have their named original owners: the
halfpoint in Q0, northwest marker in Q7, and two wall points in Q8. -/
theorem predecessor_of_missing_bottom_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forward : (owners p 4).Inside (87/50) 2)
    (missing : ¬(owners p 9).Inside 2 1)
    (C : OpenSquare) (frame : OwnerFrame p 4 C) : Predecessor C := by
  have half := corner_halfpoint_of_missing_bottom_origin p hf bottomF missing
  have markC : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have markN : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_point p hf 7 11 (by decide +kernel)
  have markL : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using marker_point p hf 8 12 (by decide +kernel)
  have wallF := (wall_auxiliaries p hb).1
  refine ⟨(frame.actual _ _).mpr markC,(frame.actual _ _).mpr P,
    (frame.actual _ _).mpr G,(frame.actual _ _).mpr forward,?_,?_,?_,?_⟩
  · intro own
    exact owners_disjoint p hf 4 0 (by decide) _ _ ⟨(frame.actual _ _).mp own,half⟩
  · intro own
    exact owners_disjoint p hf 4 7 (by decide) _ _ ⟨(frame.actual _ _).mp own,markN⟩
  · intro own
    exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨(frame.actual _ _).mp own,markL⟩
  · intro own
    exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨(frame.actual _ _).mp own,wallF⟩

/-- The actual positive-predecessor branch. Q9 may omit its origin or
own it; both alternatives preserve the same physical Q4 and Q5. -/
theorem southeast_of_positive_predecessor (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (bottomF : (owners p 9).Inside (8/5) 1)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forwardC : (owners p 4).Inside (87/50) 2)
    (forwardJ : (owners p 5).Inside 2 (87/50))
    (C J : OpenSquare) (frameC : OwnerFrame p 4 C) (frameJ : OwnerFrame p 5 J)
    (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c)
    (dp : 0<J.c) (tn : 0≤J.s) : ¬(owners p 5).Inside 2 1 := by
  classical
  by_cases origin : (owners p 9).Inside 2 1
  · exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,origin⟩
  · have h := predecessor_of_missing_bottom_origin p hf hb bottomF P G forwardC origin C frameC
    have markJ : (owners p 5).Inside (47/20) (33/20) := by
      simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
    have noOrigin := previous_origin_excluded C J
      (by rw [frameC.side]; exact side_gt p 4)
      (frameC.side.trans ((side_same p 4 5).trans frameJ.side.symm))
      cp sn order dp tn h ((frameJ.actual _ _).mpr markJ) ((frameJ.actual _ _).mpr forwardJ)
      (fun x y both => owners_disjoint p hf 4 5 (by decide) x y
        ⟨(frameC.actual x y).mp both.1,(frameJ.actual x y).mp both.2⟩)
    exact fun own => noOrigin ((frameJ.actual _ _).mpr own)

/-- Named outstanding producer for the whole OOOO sign split. Its
conclusion is the genuine predecessor halfpoint, not the desired D
exclusion. A local negative-negative transfer alone does not supply it. -/
def NonpositiveHalfpoint (p : NormalizedPacking) : Prop :=
  ∀ C : OpenSquare,OwnerFrame p 4 C → 0<C.c → |C.s|≤C.c → C.s≤0 →
    (owners p 4).Inside 1 (3/2)

/-- Theorem 1's actual bottom-wall split, conditional solely on the
separately stated global nonpositive halfpoint producer. The predecessor
forward point and positive sign are derived, rather than postulated. -/
theorem southeast_of_nonpositive_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (empty : ∀ k,¬Missing p k)
    (P : (owners p 4).Inside 1 (87/50))
    (G : (owners p 4).Inside 1 (8/5))
    (forwardJ : (owners p 5).Inside 2 (87/50))
    (J : OpenSquare) (frameJ : OwnerFrame p 5 J) (dp : 0<J.c) (tn : 0≤J.s)
    (negativeHalfpoint : NonpositiveHalfpoint p) : ¬(owners p 5).Inside 2 1 := by
  classical
  have bottomF := (ordinary_walls p hb empty).2.1.1
  by_cases origin : (owners p 9).Inside 2 1
  · exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,origin⟩
  · have forwardC : (owners p 4).Inside (87/50) 2 := by
      by_contra missing
      exact origin (C1092MPPMPositiveSeedsActual.bottom_origin_of_missing p hf hb bottomF P G missing)
    obtain ⟨C,frameC,cp,range⟩ := exists_owner_frame p 4
    have positive : 0<C.s := by
      apply lt_of_not_ge
      intro nonpositive
      have half := negativeHalfpoint C frameC cp range nonpositive
      exact origin (C1092MPPMPositiveSeedsActual.bottom_origin_of_halfpoint p hf bottomF half)
    exact southeast_of_positive_predecessor p hf hb bottomF P G forwardC forwardJ
      C J frameC frameJ cp positive.le (le_trans (le_abs_self C.s) range) dp tn

#print axioms corner_halfpoint_of_missing_bottom_origin
#print axioms southeast_of_positive_predecessor
#print axioms southeast_of_nonpositive_halfpoint
end N12Compact.C1092MPPMForwardPositiveD
