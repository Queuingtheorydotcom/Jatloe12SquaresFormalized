import Compact.Completion.C1092.MPPMActualInwardSuccessor
import Compact.Completion.C1092.MPPMInwardFinalOuterOwned
import Compact.Completion.C1092.MPPMCenteredPositiveSuccessor
import Compact.Completion.C1092.MPPMCenteredPositiveHeight

/-! Genuine original point producers for CENTERED-POSITIVE-INWARD.
The outer G omission is proved from nonordinariness and the real Q9
segment before the sharp point is invoked. No opposite type is needed.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem nonnegative_outer_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c C.s) :
    ¬(owners p 4).Inside 1 (8/5) := by
  intro outer
  exact outer_nonnegative_impossible C (chart p 9) (by rw [c.side]; exact side_gt p 4)
    (central_anchors p hf C c).1 (by rw [c.actual]; norm_num; exact inward.2)
    (by rw [c.actual]; norm_num; exact outer)
    (by rw [c.actual]; norm_num; exact fun own => nonordinary ⟨own,outer⟩)
    (bottom_bar p hf hb) (Frame.apart hf c (chart_frame p 9) (by decide)) cn

theorem centered_positive_data (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (C E : OpenSquare) (c : Frame p 4 C) (e : Frame p 5 E) (cn : Normal C.c C.s) :
    C1092MPPMCenteredPositive.Input C E := by
  have empty := C1092MPPMActualWallReduction.no_missing p hf hb
  have pair := C1092MPPMInwardNeighbors.southeast_pair p hf hb empty inward
  have anchors := central_anchors p hf C c
  have outerMissing := nonnegative_outer_missing p hf hb inward nonordinary C c cn
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_owned p hf 5 9 (by decide +kernel)
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_owned p hf 9 13 (by decide +kernel)
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  refine
    { marker := anchors.1
      northMarker := anchors.2.2
      center := by rw [c.actual]; norm_num; exact center
      crosspoint := by
        rw [c.actual]; norm_num
        exact C1092MPPMInwardNeighbors.southwest_crosspoint p hf hb empty inward
      inward := by rw [c.actual]; norm_num; exact inward.1
      tip := by rw [c.actual]; norm_num; exact missing_outer_sharp p hf inward outerMissing
      successorMarker := by rw [e.actual]; norm_num; exact em
      near := by rw [e.actual]; norm_num; exact pair.2
      outer := by rw [e.actual]; norm_num; exact pair.1
      halfpoint := by rw [e.actual]; norm_num; exact successor_halfpoint p hf hb inward
      shortWall := ?_
      bottomMarker := ?_
      corner := ?_
      rightOrigin := ?_
      rightG := ?_
      apart := Frame.apart hf c e (by decide) }
  · exact fun own => Frame.apart hf e (chart_frame p 10) (by decide) _ _
      ⟨own,right_bar p hf hb inward (-39/100) (by norm_num) (by norm_num)⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bm⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 1 (by decide) _ _ ⟨own,corner⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 10 (by decide) _ _ ⟨own,right_origin p hf hb inward⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 10 (by decide) _ _
      ⟨own,(C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2⟩

theorem centered_positive_bounds (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c C.s) :
    99/100<C.c ∧ C.s<7/50 ∧
      93/500+(33/50)*C.s<C.loV+C.side ∧ C.loU+C.side≤(7/50)*C.c-C.s/2 := by
  obtain ⟨E,e,ep,canonical⟩ := canonical_frame p 5
  exact C1092MPPMCenteredPositive.bounds C E (by rw [c.side]; exact side_gt p 4)
    (c.side.trans ((side_same p 4 5).trans e.side.symm)) cn ep canonical
    (centered_positive_data p hf hb inward nonordinary center C E c e cn)

/-- Both actual ordinary neighbors impose incompatible bounds on the
same centered positive C. No opposite owner is an input to this ending. -/
theorem centered_nonnegative_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c C.s) : False := by
  have bounds := centered_positive_bounds p hf hb inward nonordinary center C c cn
  obtain ⟨W,w,wp,canonical⟩ := canonical_frame p 7
  have upper := C1092MPPMCenteredPositive.height C W
    (by rw [c.side]; exact side_gt p 4)
    (c.side.trans ((side_same p 4 7).trans w.side.symm)) cn bounds.1 bounds.2.1
    (by rw [c.actual]; norm_num; exact center) (central_anchors p hf C c).1 bounds.2.2.2
    (predecessor_points p hf hb inward W w) canonical (Frame.apart hf c w (by decide))
  linarith only [bounds.2.1,bounds.2.2.1,upper]

theorem centered_sign (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (C : OpenSquare) (c : Frame p 4 C) (canonical : |C.s|≤C.c) : C.s<0 := by
  apply lt_of_not_ge
  intro sign
  exact centered_nonnegative_impossible p hf hb inward nonordinary center C c
    ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,C.unit_normal⟩

end
#print axioms nonnegative_outer_missing
#print axioms centered_positive_data
#print axioms centered_positive_bounds
#print axioms centered_nonnegative_impossible
#print axioms centered_sign
end N12Compact.C1092MPPMActualInward
