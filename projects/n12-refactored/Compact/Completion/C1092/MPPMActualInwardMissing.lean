import Compact.Completion.C1092.MPPMActualInwardPoints
import Compact.Completion.C1092.MPPMInwardFinalOuterOwned
import Compact.Completion.C1092.MPPMInwardFinalBottomAngle
import S12.AuxCoverGeometry

/-! The two distinct genuine missing-center alternatives in original
MPPM. An outer-owned square uses its own F omission and the actual short
Q9 bar. An outer-omitted square uses the rotated strict duplicate point,
the actual Q9 far reach and Q9's original closed center sign.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem outer_owned_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (outer : (owners p 4).Inside 1 (8/5)) (missing : ¬(owners p 4).Inside 2 2)
    (C : OpenSquare) (frame : Frame p 4 C) : OuterOwnedInput C (chart p 9) := by
  have cm : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_owned p hf 4 8 (by decide +kernel)
  refine ⟨by rw [frame.side]; exact side_gt p 4,?_,?_,?_,?_,?_,?_,
    bottom_bar p hf hb,Frame.apart hf frame (chart_frame p 9) (by decide)⟩
  · rw [frame.actual]; norm_num; exact cm
  · rw [frame.actual]; norm_num; exact inward.1
  · rw [frame.actual]; norm_num; exact inward.2
  · rw [frame.actual]; norm_num; exact outer
  · rw [frame.actual]; norm_num; exact missing
  · rw [frame.actual]; norm_num
    exact fun own => nonordinary ⟨own,outer⟩

/-- The profile, radical angle bound, strict halfpoint and actual bottom
origin are all produced from this owner's own G membership. -/
theorem outer_owned (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (outer : (owners p 4).Inside 1 (8/5)) (missing : ¬(owners p 4).Inside 2 2)
    (C : OpenSquare) (frame : Frame p 4 C) (canonical : |C.s|≤C.c) :
    MissingProfile C ∧ half C.c (-C.s)<1-Real.sqrt 13/5 ∧
      (owners p 4).Inside 1 (3/2) ∧ (owners p 9).Inside 2 1 := by
  have input := outer_owned_input p hf hb inward nonordinary outer missing C frame
  have profile := outer_owned_profile C (chart p 9) input canonical
  have point := outer_owned_halfpoint C (chart p 9) input canonical
  have actual := (frame.actual _ _).mp point
  norm_num at actual
  have origin := C1092MPPMPositiveSeedsActual.bottom_origin_of_halfpoint p hf
    (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.1.1 actual
  exact ⟨profile.1,profile.2.1,actual,origin⟩

theorem outer_omitted_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (outer : ¬(owners p 4).Inside 1 (8/5)) (missing : ¬(owners p 4).Inside 2 2)
    (C : OpenSquare) (frame : Frame p 4 C) (cn : Normal C.c (-C.s)) :
    BottomAngle.Input C (chart p 9) := by
  have empty := C1092MPPMActualWallReduction.no_missing p hf hb
  have cm : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_owned p hf 4 8 (by decide +kernel)
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using marker_owned p hf 9 13 (by decide +kernel)
  refine
    { side := by rw [frame.side]; exact side_gt p 4
      same := frame.side.trans (side_same p 4 9)
      normal := cn
      marker := by rw [frame.actual]; norm_num; exact cm
      inner := by rw [frame.actual]; norm_num; exact inward.1
      forward := by rw [frame.actual]; norm_num; exact inward.2
      crosspoint := by
        rw [frame.actual]; norm_num
        exact C1092MPPMInwardNeighbors.southwest_crosspoint p hf hb empty inward
      sharp := by
        rw [frame.actual]; norm_num
        exact missing_outer_sharp p hf inward outer
      origin := by rw [frame.actual]; norm_num; exact missing
      outer := by rw [frame.actual]; norm_num; exact outer
      bottomMarker := by rw [(chart_frame p 9).actual]; norm_num; exact bm
      bottomNear := by
        rw [(chart_frame p 9).actual]; norm_num
        exact (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.1.2
      bottomFar := by
        rw [(chart_frame p 9).actual]; norm_num
        exact C1092MPPMInwardNeighbors.bottom_far p hf hb empty inward
      wall := ?_
      center := ?_
      apart := Frame.apart hf frame (chart_frame p 9) (by decide) }
  · intro x y own
    have actual := ((chart_frame p 9).actual x y).mp own
    have bound := (p.contained _ _ _ actual).2.2.1
    linarith only [bound]
  · have cut := (hb 1).1
    have actual : centerX (owners p 9)≤2 := by
      simpa [mppm,C1092WallCycle.wallFrame,C1092WallCycle.localFrame,
        C1092WallCycle.wallOwner] using cut
    change centerX ((owners p 9).translated 2 2)≤0
    rw [center_translate_x]
    linarith only [actual]

/-- The previously raw bottom-angle theorem now has every point, wall,
center and ownership hypothesis produced by the original family. -/
theorem outer_omitted_angle (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (outer : ¬(owners p 4).Inside 1 (8/5)) (missing : ¬(owners p 4).Inside 2 2)
    (C : OpenSquare) (frame : Frame p 4 C) (cn : Normal C.c (-C.s)) :
    0<half C.c (-C.s) ∧ half C.c (-C.s)<1-2*Real.sqrt 5/5 ∧
      half C.c (-C.s)<53/500 :=
  BottomAngle.angle C (chart p 9) (outer_omitted_input p hf hb inward outer missing C frame cn)

end
#print axioms outer_owned
#print axioms outer_omitted_input
#print axioms outer_omitted_angle
end N12Compact.C1092MPPMActualInward
