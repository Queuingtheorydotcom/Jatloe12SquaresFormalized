import Compact.Completion.C1092.MPPMActualProfiles
import Compact.Completion.C1092.MPPMNorthwestActualSign
import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNorthwestGeometry
import Compact.Completion.C1092.MMMP.UpperThird
import Compact.Completion.C1092.TwoFifthsEnding

/-! The actual MPPM right-near one-omission ending. Every square is in
the common chart (x,y) ↦ (2+y,2+x): W/N/E/R are original Q5/Q6/Q7/Q11.
The positive W frame is the MPPM frame, with its genuine mixed-bottom
center cut. Its height and floor are derived from the actual E square
and the whole actual Q9 bar, before applying the shared upper-third
argument. No MMMP wall context is transferred.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualTwoFifths
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MMMPTwoFifthsEntrance
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

theorem upper_third (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3)
    (N : OpenSquare) (np : C1092MPPMUpperSign.PositiveActual p N) :
    3*N.s<1+N.c := by
  obtain ⟨E,ep,e,cap⟩ := C1092MPPMActualProfiles.southeast_profile p hf hb omitted near N np
  obtain ⟨W,wp⟩ := C1092MPPMNorthwestActualSign.exists_positive p hf hb omitted
  have pair := omitted_bottom_inward p hf hb omitted
  have bar := omitted_bottom_bar p hf hb omitted
  have wm : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  have sw : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  have ne : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using mark p hf 6 10 (by decide +kernel)
  have origin : W.Inside 0 0 := by
    apply (wp.actual _ _).mpr
    norm_num
    exact C1092MPPMOmissionCenter.bottom_center p hf hb omitted
  have left : W.Inside (-13/50) 0 := by
    apply (wp.actual _ _).mpr
    norm_num
    exact pair.1
  have north : W.Inside 0 (13/50) := by
    apply (wp.actual _ _).mpr
    norm_num
    exact pair.2
  have diagonal : W.Inside (-1/2) (1/2) := by
    apply (wp.actual _ _).mpr
    norm_num
    exact (C1092MPPMPointCore.diagonal p hf hb omitted).1
  have marker : W.Inside (-7/20) (7/20) := by
    apply (wp.actual _ _).mpr
    norm_num
    exact wm
  have missingSW : ¬W.Inside (-7/20) (-7/20) := by
    intro own
    have original := (wp.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨original,sw⟩
  have missingNE : ¬W.Inside (7/20) (7/20) := by
    intro own
    have original := (wp.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨original,ne⟩
  have missingLeft : ¬W.Inside (-1) (39/100) := by
    intro own
    have original := (wp.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨original,bar _ (by norm_num) (by norm_num)⟩
  have missingFar : ¬W.Inside (-1) (2/5) := by
    intro own
    have original := (wp.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 9 (by decide) _ _
      ⟨original,bar _ (by norm_num) (by norm_num)⟩
  have sameEW : E.side=W.side := ep.side.trans ((side_same p 7 5).trans wp.side.symm)
  have apartEW : ∀ x y,¬(E.Inside x y ∧ W.Inside x y) := fun x y both =>
    owners_disjoint p hf 7 5 (by decide) _ _
      ⟨(ep.actual _ _).mp both.1,(wp.actual _ _).mp both.2⟩
  have height := positive_northwest_height E W e sameEW wp.normal
    (southeast_height E e cap) origin left north apartEW
  have side : 1<W.side := by rw [wp.side]; exact side_gt p 5
  have angle := positive_northwest_faces W side wp.normal origin diagonal
    missingSW missingNE missingLeft
  have floor := positive_northwest_left_face W wp.normal angle height origin missingFar
  exact C1092MMMPUpperThird.upper_third W N side
    (wp.side.trans ((side_same p 5 6).trans np.side.symm))
    wp.normal angle origin marker (by linarith only [height]) floor
    (C1092MPPMActualProfiles.northeast_core p hf hb omitted N np)
    (fun x y both => owners_disjoint p hf 5 6 (by decide) _ _
      ⟨(wp.actual _ _).mp both.1,(np.actual _ _).mp both.2⟩)

/-- Original Q7 and Q6 forbid the two closed small-slope intervals of
the same original Q11. Its orientation is arbitrary. -/
theorem impossible_of_top_g4 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (near : (owners p 11).Inside (87/50) 3) : False := by
  obtain ⟨N,np⟩ := C1092MPPMUpperSign.exists_positive p hf hb omitted
  obtain ⟨E,ep,e,_⟩ := C1092MPPMActualProfiles.southeast_profile p hf hb omitted near N np
  let R := (pullSwap (owners p 11)).translated 2 2
  have actual (x y : ℝ) : R.Inside x y↔(owners p 11).Inside (2+y) (2+x) := by
    rw [R,inside_translated_iff,inside_pullSwap]
  have sameER : E.side=R.side := ep.side.trans (side_same p 7 11)
  have sameNR : N.side=R.side := np.side.trans (side_same p 6 11)
  apply C1092TwoFifths.impossible E N R
  exact ⟨e,
    (C1092MPPMActualProfiles.northeast_core p hf hb omitted N np).complete
      (upper_third p hf hb omitted near N np).le,
    C1092MPPMActualProfiles.right_profile p hf hb omitted near,
    sameER,sameNR,
    fun x y both => owners_disjoint p hf 7 11 (by decide) _ _
      ⟨(ep.actual _ _).mp both.1,(actual _ _).mp both.2⟩,
    fun x y both => owners_disjoint p hf 6 11 (by decide) _ _
      ⟨(np.actual _ _).mp both.1,(actual _ _).mp both.2⟩⟩

/-- The normalized actual bottom-forward omission is impossible,
including both strict-membership alternatives for original Q11 G4. -/
theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) : False := by
  by_cases near : (owners p 11).Inside (87/50) 3
  · exact impossible_of_top_g4 p hf hb omitted near
  · exact C1092MPPMActualOneOmission.impossible_of_top_g4_omission p hf hb omitted near

end
#print axioms upper_third
#print axioms impossible_of_top_g4
#print axioms impossible
end N12Compact.C1092MPPMActualTwoFifths
