import Compact.Completion.C1092.MPPMActualInwardMissing
import Compact.Completion.C1092.MPPMActualInwardSuccessor
import Compact.Completion.C1092.MPPMInwardOuterFar
import Compact.Completion.C1092.MPPMInwardOmittedFar
import Compact.Completion.C1092.MPPMOrdinaryWallAdvance

/-! The ordinary-opposite alternatives, with genuine original wall
advance. Actual Q6 F9 produces the entire Q10 far bar. The three local
endings retain their distinct center/G alternatives and use only the
origins that those same alternatives actually produce. Source only. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem ordinary_opposite_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (opposite : (owners p 6).Inside 3 (113/50)) :
    ∀ y : ℝ,-14/25≤y → y≤0 → (chart p 10).Inside 1 y := by
  have far := C1092MPPMOrdinaryWallAdvance.right_far_no_omission p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) opposite
  have origin := right_origin p hf hb inward
  have segment := Completion.OtherCases.WallProfile.vertical_owned (owners p 10)
    3 (36/25) 2 (by norm_num) far origin
  intro y low high
  rw [(chart_frame p 10).actual]
  norm_num
  exact segment _ (by linarith only [low]) (by linarith only [high])

theorem outer_far_input (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (opposite : (owners p 6).Inside 3 (113/50))
    (origin : (owners p 9).Inside 2 1)
    (C E : OpenSquare) (c : Frame p 4 C) (e : Frame p 5 E)
    (cn : Normal C.c (-C.s)) (canonical : |E.s|≤E.c) :
    C1092MPPMInwardOuterFar.Input C E (chart p 10) := by
  refine
    { side := by rw [c.side]; exact side_gt p 4
      normal := cn
      marker := (central_anchors p hf C c).1
      inner := by rw [c.actual]; norm_num; exact inward.1
      crosspoint := by
        rw [c.actual]; norm_num
        exact C1092MPPMInwardNeighbors.southwest_crosspoint p hf hb
          (C1092MPPMActualWallReduction.no_missing p hf hb) inward
      floor := (negative_faces p hf inward nonordinary C c cn).1
      successor := (successor_profile p hf hb inward nonordinary C E c e cn canonical).2
      same := c.side.trans ((side_same p 4 5).trans e.side.symm)
      apart := Frame.apart hf c e (by decide)
      bottom := ?_
      bar := ordinary_opposite_bar p hf hb inward opposite
      apartBar := Frame.apart hf e (chart_frame p 10) (by decide) }
  rw [e.actual]; norm_num
  exact fun own => owners_disjoint p hf 5 9 (by decide) _ _ ⟨own,origin⟩

theorem missing_outer_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (outer : (owners p 4).Inside 1 (8/5)) (missing : ¬(owners p 4).Inside 2 2)
    (opposite : (owners p 6).Inside 3 (113/50)) : False := by
  obtain ⟨C,c,cp,canonicalC⟩ := canonical_frame p 4
  obtain ⟨E,e,ep,canonicalE⟩ := canonical_frame p 5
  have raw := outer_owned_profile C (chart p 9)
    (outer_owned_input p hf hb inward nonordinary outer missing C c) canonicalC
  have actual := outer_owned p hf hb inward nonordinary outer missing C c canonicalC
  have input := outer_far_input p hf hb inward nonordinary opposite actual.2.2.2
    C E c e raw.1.normal canonicalE
  exact C1092MPPMInwardOuterFar.missing_center_impossible C E (chart p 10) input
    raw.2.2.le raw.1.upperV

theorem centered_outer_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (outer : (owners p 4).Inside 1 (8/5)) (opposite : (owners p 6).Inside 3 (113/50))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c (-C.s)) (negative : C.s<0) : False := by
  obtain ⟨E,e,ep,canonical⟩ := canonical_frame p 5
  have bounds := centered_negative p hf hb inward nonordinary center C c cn negative
  have origin := (bounds.2.2.2.2 outer).2
  have input := outer_far_input p hf hb inward nonordinary opposite origin C E c e cn canonical
  exact C1092MPPMInwardOuterFar.centered_impossible C E (chart p 10) input
    bounds.2.2.1.le bounds.2.1.le

theorem centered_omitted_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (outer : ¬(owners p 4).Inside 1 (8/5)) (opposite : (owners p 6).Inside 3 (113/50))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c (-C.s)) (negative : C.s<0) : False := by
  obtain ⟨E,e,ep,canonical⟩ := canonical_frame p 5
  have bounds := centered_negative p hf hb inward nonordinary center C c cn negative
  have side : 1<C.side := by rw [c.side]; exact side_gt p 4
  have marker := (central_anchors p hf C c).1
  have localOuter : ¬C.Inside (-1) (-2/5) := by rw [c.actual]; norm_num; exact outer
  have floor := C1092MPPMInwardOmittedFar.omitted_lower C side cn marker
    bounds.2.2.1.le bounds.2.1.le localOuter
  apply C1092MPPMInwardOmittedFar.impossible C E (chart p 10)
  exact
    { side := side
      same := c.side.trans ((side_same p 4 5).trans e.side.symm)
      normal := cn
      small := bounds.2.2.1.le
      lowerU := floor
      height := bounds.2.1.le
      marker := marker
      crosspoint := by
        rw [c.actual]; norm_num
        exact C1092MPPMInwardNeighbors.southwest_crosspoint p hf hb
          (C1092MPPMActualWallReduction.no_missing p hf hb) inward
      successor := (successor_profile p hf hb inward nonordinary C E c e cn canonical).2
      bar := ordinary_opposite_bar p hf hb inward opposite
      apart := Frame.apart hf c e (by decide)
      apartBar := Frame.apart hf e (chart_frame p 10) (by decide) }

theorem centered_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (opposite : (owners p 6).Inside 3 (113/50))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c (-C.s)) (negative : C.s<0) : False := by
  by_cases outer : (owners p 4).Inside 1 (8/5)
  · exact centered_outer_far p hf hb inward nonordinary center outer opposite C c cn negative
  · exact centered_omitted_far p hf hb inward nonordinary center outer opposite C c cn negative

end
#print axioms ordinary_opposite_bar
#print axioms missing_outer_far
#print axioms centered_far
end N12Compact.C1092MPPMActualInward
