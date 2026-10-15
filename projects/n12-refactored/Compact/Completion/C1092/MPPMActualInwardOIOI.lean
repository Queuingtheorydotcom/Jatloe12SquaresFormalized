import Compact.Completion.C1092.MPPMActualInwardPredecessor

/-! The two completed OIOI endings, joined to their original owners.
The explicit alternatives are only point ownership and canonical sign
cases; all profiles, origins, support caps and foreign bars are produced
inside these proofs. The earlier exhaustive inward classification is a
separate producer, not asserted by these local actual-packing theorems.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

/-- The centered southwest owner is impossible when its opposite is
genuinely inward and owns its outer G9. The opposite center omission is
derived from the same physical center owned by Q4. -/
theorem centered_oioi (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4)) (center : (owners p 4).Inside 2 2)
    (northInward : (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2)
    (northNonordinary : ¬((owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5)))
    (northOuter : (owners p 6).Inside 3 (12/5))
    (C : OpenSquare) (c : Frame p 4 C) (cn : Normal C.c (-C.s)) (negative : C.s<0) :
    False := by
  have northMissing : ¬(owners p 6).Inside 2 2 :=
    fun own => owners_disjoint p hf 4 6 (by decide) _ _ ⟨center,own⟩
  obtain ⟨W,w,pred⟩ := opposite_predecessor p hf hb northInward northNonordinary
    northOuter northMissing C c
  obtain ⟨E,e,ep,ecanonical⟩ := canonical_frame p 5
  have cap := centered_input p hf hb inward nonordinary center C E W c e w cn ecanonical
  have wn : |W.s|≤W.c := by
    rw [abs_of_nonpos (by linarith only [pred.normal.1] : W.s≤0)]
    exact pred.normal.2.1
  have input : CenteredPredecessor C W :=
    { side := cap.side
      same := pred.same
      central := cn
      centralNegative := negative
      predecessor := pred.normal
      center := cap.center
      marker := cap.marker
      previousMarker := pred.marker
      markerCap := cap.upperA
      firstCap := cap.firstCap
      halfSmall := centered_half_angle C W cap wn
      lowerU := pred.lowerU
      lowerV := pred.lowerV
      upperV := pred.upperV
      apart := pred.apart }
  have successor := (successor_profile p hf hb inward nonordinary C E c e cn ecanonical).2
  have lower := (negative_faces p hf inward nonordinary C c cn).1
  exact centered_impossible C W E (chart p 10) (chart p 9) (chart p 0) input
    (c.side.trans ((side_same p 4 5).trans e.side.symm)) successor
    (by rw [c.actual]; norm_num; exact inward.1)
    (by linarith only [lower]) (inward_right_bar p hf hb inward northOuter northInward.2)
    (bottom_corner p hf hb) (Frame.apart hf c e (by decide))
    (Frame.apart hf e (chart_frame p 10) (by decide))
    (Frame.apart hf c (chart_frame p 0) (by decide))
    (Frame.apart hf e (chart_frame p 9) (by decide))

/-- Both opposite inward owners omit the center and own their own outer
G points. No sign premise remains: their negative profiles are derived
from the exact outer-owned arguments. -/
theorem opposed_missing_oioi (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (nonordinary : ¬Ordinary (owners p 4))
    (outer : (owners p 4).Inside 1 (8/5)) (missing : ¬(owners p 4).Inside 2 2)
    (northInward : (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2)
    (northNonordinary : ¬((owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5)))
    (northOuter : (owners p 6).Inside 3 (12/5))
    (northMissing : ¬(owners p 6).Inside 2 2) : False := by
  obtain ⟨C,c,cp,ccanonical⟩ := canonical_frame p 4
  have central := outer_owned p hf hb inward nonordinary outer missing C c ccanonical
  obtain ⟨W,w,pred⟩ := opposite_predecessor p hf hb northInward northNonordinary
    northOuter northMissing C c
  obtain ⟨E,e,ep,ecanonical⟩ := canonical_frame p 5
  have successor := (successor_profile p hf hb inward nonordinary C E c e
    central.1.normal ecanonical).2
  exact missing_impossible C W E (chart p 9) (chart p 10) central.1 pred
    (c.side.trans ((side_same p 4 5).trans e.side.symm)) successor
    (inward_bottom_long_bar p hf hb inward central.2.2.2)
    (inward_right_bar p hf hb inward northOuter northInward.2)
    (Frame.apart hf c (chart_frame p 9) (by decide)) (Frame.apart hf c e (by decide))
    (Frame.apart hf e (chart_frame p 10) (by decide))
    (Frame.apart hf e (chart_frame p 9) (by decide))

end
#print axioms centered_oioi
#print axioms opposed_missing_oioi
end N12Compact.C1092MPPMActualInward
