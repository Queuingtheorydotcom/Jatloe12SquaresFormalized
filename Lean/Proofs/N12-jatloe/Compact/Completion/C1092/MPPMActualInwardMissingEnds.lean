import Compact.Completion.C1092.MPPMActualInwardPositiveMissing
import Compact.Completion.C1092.MPPMActualInwardSymmetry
import Compact.Completion.C1092.MPPMInwardPositiveOriginEnding
import Compact.Completion.C1092.MPPMInwardPositiveFarEnding
import Compact.Completion.C1092.MPPMActualInwardFar
import Compact.Completion.C1092.MPPMInwardSmallThreeEnding

/-! Actual missing-center inward endings. Each orientation branch uses
only the boundary origin or bar proved for its own literal opposite
alternative. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem positive_missing_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (missing : ¬(owners p 4).Inside 2 2)
    (north : NorthInward p) (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c C.s) :
    False := by
  obtain ⟨E,e,ep,canonical⟩ := canonical_frame p 5
  have input := positive_missing_input p hf hb inward nonordinary missing C E c e cn
  have origin := opposite_inward_left_origin p hf hb north
  exact C1092MPPMInwardPositive.origin_impossible C E input canonical (by
    rw [c.actual]; norm_num
    exact fun own => owners_disjoint p hf 4 8 (by decide) _ _ ⟨own,origin⟩)

theorem positive_missing_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (missing : ¬(owners p 4).Inside 2 2)
    (opposite : (owners p 6).Inside 3 (113/50))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c C.s) : False := by
  obtain ⟨E,e,ep,canonical⟩ := canonical_frame p 5
  have input := positive_missing_input p hf hb inward nonordinary missing C E c e cn
  have far : ¬E.Inside 1 (-14/25) := fun own =>
    Frame.apart hf e (chart_frame p 10) (by decide) _ _
      ⟨own,ordinary_opposite_bar p hf hb inward opposite _ le_rfl (by norm_num)⟩
  have seeds := left_seed_points p hf hb
  exact C1092MPPMInwardPositive.far_impossible C E (chart p 8) input canonical far
    seeds.1 seeds.2 (Frame.apart hf c (chart_frame p 8) (by decide))

theorem nonpositive_missing_omitted (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (missing : ¬(owners p 4).Inside 2 2)
    (outer : ¬(owners p 4).Inside 1 (8/5))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c (-C.s)) : False := by
  obtain ⟨E,e,ep,canonical⟩ := canonical_frame p 5
  apply C1092MPPMInwardSmallThree.impossible C (chart p 9) E
  exact
    { bottom := outer_omitted_input p hf hb inward outer missing C c cn
      sameE := c.side.trans ((side_same p 4 5).trans e.side.symm)
      successor := (successor_profile p hf hb inward nonordinary C E c e cn canonical).2
      apartCE := Frame.apart hf c e (by decide)
      apartBE := Frame.apart hf (chart_frame p 9) e (by decide) }

/-- Every missing-center genuinely inward owner owns its own outer G.
Both signs and both actual opposite pairs are exhausted before any
opposite sign or center claim is made. In particular the origin branch
uses only the opposite inward pair, so this classification is acyclic. -/
theorem missing_center_outer (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (missing : ¬(owners p 4).Inside 2 2) :
    (owners p 4).Inside 1 (8/5) := by
  by_contra outer
  obtain ⟨C,c,cp,canonical⟩ := canonical_frame p 4
  by_cases sign : 0≤C.s
  · have cn : Normal C.c C.s :=
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,C.unit_normal⟩
    rcases north_cover p hf hb with ordinary|north
    · exact positive_missing_far p hf hb inward nonordinary missing ordinary.1 C c cn
    · exact positive_missing_origin p hf hb inward nonordinary missing north C c cn
  · have negative : C.s<0 := lt_of_not_ge sign
    have cn : Normal C.c (-C.s) := ⟨by linarith only [negative],
      by simpa only [abs_of_neg negative] using canonical,by nlinarith only [C.unit_normal]⟩
    exact nonpositive_missing_omitted p hf hb inward nonordinary missing outer C c cn

end
#print axioms positive_missing_origin
#print axioms positive_missing_far
#print axioms nonpositive_missing_omitted
#print axioms missing_center_outer
end N12Compact.C1092MPPMActualInward
