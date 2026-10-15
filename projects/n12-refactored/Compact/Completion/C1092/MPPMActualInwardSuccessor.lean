import Compact.Completion.C1092.MPPMActualInwardPoints
import Compact.Completion.C1092.MPPMInwardFinalSign
import Compact.Completion.C1092.MPPMInwardFinalAngle

/-! The actual negative inward owner produces its successor's sign and
full bar profile. This then supplies the centered cap and angle input;
none of those support inequalities is an extra entrance assumption.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem central_anchors (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (C : OpenSquare) (frame : Frame p 4 C) :
    C.Inside (-7/20) (-7/20) ∧ ¬C.Inside (7/20) (-7/20) ∧ ¬C.Inside (-7/20) (7/20) := by
  have cm : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_owned p hf 4 8 (by decide +kernel)
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_owned p hf 5 9 (by decide +kernel)
  have wm : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_owned p hf 7 11 (by decide +kernel)
  refine ⟨?_,?_,?_⟩
  · rw [frame.actual]; norm_num; exact cm
  · rw [frame.actual]; norm_num
    exact fun own => owners_disjoint p hf 4 5 (by decide) _ _ ⟨own,em⟩
  · rw [frame.actual]; norm_num
    exact fun own => owners_disjoint p hf 4 7 (by decide) _ _ ⟨own,wm⟩

theorem negative_faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (inward : Inward (owners p 4)) (nonordinary : ¬Ordinary (owners p 4))
    (C : OpenSquare) (frame : Frame p 4 C) (cn : Normal C.c (-C.s)) :
    -C.c-(13/50)*C.s≤C.loU ∧ C.loV+C.side≤(7/20)*(C.c+C.s) := by
  have anchors := central_anchors p hf C frame
  have side : 1<C.side := by rw [frame.side]; exact side_gt p 4
  have I : C.Inside 0 (-13/50) := by rw [frame.actual]; norm_num; exact inward.1
  have J : C.Inside (-13/50) 0 := by rw [frame.actual]; norm_num; exact inward.2
  have nonordinaryC : ¬(C.Inside (-1) (-13/50) ∧ C.Inside (-1) (-2/5)) := by
    intro own
    apply nonordinary
    constructor
    · have actual := (frame.actual _ _).mp own.1; norm_num at actual; exact actual
    · have actual := (frame.actual _ _).mp own.2; norm_num at actual; exact actual
  have height : C.loV+C.side≤(7/20)*(C.c+C.s) := by
    by_cases center : C.Inside 0 0
    · exact (centered_marker_caps C side cn center anchors.1 anchors.2.1 anchors.2.2).2
    · have cb := normal_bounds cn
      have zero : C.loV+C.side≤0 := by
        apply le_of_not_gt
        intro high
        apply center
        refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [J.1,I.2.1,anchors.1.2.2.1,high,cb.1,cn.1,cn.2.1]
      linarith only [zero,cn.2.1]
  exact ⟨centered_lower_face C side cn anchors.1 I height nonordinaryC,height⟩

theorem successor_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (C E : OpenSquare) (c : Frame p 4 C) (e : Frame p 5 E)
    (cn : Normal C.c (-C.s)) : SignInput C E := by
  have empty := C1092MPPMActualWallReduction.no_missing p hf hb
  have pair := C1092MPPMInwardNeighbors.southeast_pair p hf hb empty inward
  have anchors := central_anchors p hf C c
  have faces := negative_faces p hf inward nonordinary C c cn
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_owned p hf 5 9 (by decide +kernel)
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_owned p hf 9 13 (by decide +kernel)
  have km : (owners p 1).Inside 3 (457/500) := by
    simpa [marker] using marker_owned p hf 1 2 (by decide +kernel)
  have kp : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  refine
    { side := by rw [c.side]; exact side_gt p 4
      same := c.side.trans ((side_same p 4 5).trans e.side.symm)
      central := cn
      lowerA := by linarith only [faces.1]
      upperH := faces.2
      marker := anchors.1
      inner := by rw [c.actual]; norm_num; exact inward.1
      crosspoint := by
        rw [c.actual]; norm_num
        exact C1092MPPMInwardNeighbors.southwest_crosspoint p hf hb empty inward
      successorMarker := by rw [e.actual]; norm_num; exact em
      near := by rw [e.actual]; norm_num; exact pair.2
      outer := by rw [e.actual]; norm_num; exact pair.1
      halfpoint := by rw [e.actual]; norm_num; exact successor_halfpoint p hf hb inward
      missingInner := ?_
      missingRight := ?_
      missingBottom := ?_
      missingCorner := ?_
      missingCornerMarker := ?_
      apart := Frame.apart hf c e (by decide) }
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 4 (by decide) _ _ ⟨own,inward.1⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 10 (by decide) _ _
      ⟨own,(C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,bm⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 1 (by decide) _ _ ⟨own,kp⟩
  · rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 1 (by decide) _ _ ⟨own,km⟩

theorem successor_profile (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (C E : OpenSquare) (c : Frame p 4 C) (e : Frame p 5 E)
    (cn : Normal C.c (-C.s)) (canonical : |E.s|≤E.c) : E.s<0 ∧ NegativeSuccessor E := by
  have input := successor_input p hf hb inward nonordinary C E c e cn
  have negative := successor_negative C E input canonical
  have en : Normal E.c (-E.s) := ⟨by linarith only [negative],
    by simpa only [abs_of_neg negative] using canonical,by nlinarith only [E.unit_normal]⟩
  have origin : ¬E.Inside 1 0 := by
    rw [e.actual]; norm_num
    exact fun own => owners_disjoint p hf 5 10 (by decide) _ _ ⟨own,right_origin p hf hb inward⟩
  exact ⟨negative,negative_successor E (chart p 10)
    (by rw [e.side]; exact side_gt p 5) en negative input.successorMarker input.near input.outer
    input.halfpoint input.missingInner origin input.missingCorner input.missingBottom
    (right_bar p hf hb inward) (Frame.apart hf e (chart_frame p 10) (by decide))⟩

theorem centered_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (C E W : OpenSquare) (c : Frame p 4 C) (e : Frame p 5 E) (w : Frame p 7 W)
    (cn : Normal C.c (-C.s)) (canonicalE : |E.s|≤E.c) : CenteredCapInput C W := by
  have anchors := central_anchors p hf C c
  have side : 1<C.side := by rw [c.side]; exact side_gt p 4
  have origin : C.Inside 0 0 := by rw [c.actual]; norm_num; exact center
  have pair := centered_marker_caps C side cn origin anchors.1 anchors.2.1 anchors.2.2
  have ep := (successor_profile p hf hb inward nonordinary C E c e cn canonicalE).2
  have ce := c.side.trans ((side_same p 4 5).trans e.side.symm)
  have cw := c.side.trans ((side_same p 4 7).trans w.side.symm)
  exact ⟨side,cw,cn,origin,anchors.1,pair.1,pair.2,
    centered_first_cap C E side ce cn origin anchors.1 anchors.2.1 anchors.2.2 ep
      (Frame.apart hf c e (by decide)),
    predecessor_points p hf hb inward W w,Frame.apart hf c w (by decide)⟩

/-- The full centered-negative cap/angle conclusions now have genuine
original-owner producers. The sign is the explicit central case split. -/
theorem centered_negative (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c (-C.s)) (negative : C.s<0) :
    C.loU+C.side≤(7/50)*C.c-C.s/2 ∧ C.loV+C.side<17/125 ∧
      half C.c (-C.s)<21/100 ∧ ¬(owners p 4).Inside 1 (87/50) ∧
      ((owners p 4).Inside 1 (8/5) →
        (owners p 4).Inside 1 (3/2) ∧ (owners p 9).Inside 2 1) := by
  obtain ⟨E,e,ep,canonicalE⟩ := canonical_frame p 5
  obtain ⟨W,w,wp,canonicalW⟩ := canonical_frame p 7
  have input := centered_input p hf hb inward nonordinary center C E W c e w cn canonicalE
  have absent : ¬(C.Inside (-1) (-13/50) ∧ C.Inside (-1) (-2/5)) := by
    intro own
    apply nonordinary
    constructor
    · have actual := (c.actual _ _).mp own.1; norm_num at actual; exact actual
    · have actual := (c.actual _ _).mp own.2; norm_num at actual; exact actual
  have consequences := centered_outer_consequences C W input canonicalW negative absent
  refine ⟨input.firstCap,centered_height_cap C W input canonicalW,
    centered_half_angle C W input canonicalW,?_,?_⟩
  · intro own
    apply consequences.1
    rw [c.actual]; norm_num; exact own
  · intro own
    have localG : C.Inside (-1) (-2/5) := by rw [c.actual]; norm_num; exact own
    have point := (c.actual _ _).mp (consequences.2 localG)
    norm_num at point
    exact ⟨point,C1092MPPMPositiveSeedsActual.bottom_origin_of_halfpoint p hf
      (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.1.1 point⟩

end
#print axioms successor_profile
#print axioms centered_input
#print axioms centered_negative
end N12Compact.C1092MPPMActualInward
