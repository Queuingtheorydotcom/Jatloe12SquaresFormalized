import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNorthwest
import Compact.Completion.C1092.MMMP.UpperThird
import Compact.Completion.C1092.TwoFifthsEnding
import Compact.Completion.C1092.MMMP.ActualProfile

/-! The original MMMP branch has no remaining profile premises.  If the
actual right square owns F8, the actual southeast and northwest squares
produce the northeast upper-third bound, and the two-fifths squeeze
excludes that same right square.  Its resulting F8 omission supplies the
long right bar for the existing strong northeast ending.  The two G8
alternatives remain inside the southeast profile producer. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins
set_option Elab.async false

/-- The right near point is excluded using the original Q5, Q6, Q7 and
Q10.  Every frame is physically equivalent to its named original owner;
the common-side and disjointness hypotheses come from the packing. -/
theorem near_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50)) : False := by
  obtain ⟨E,ep,e⟩ := southeast_profile p hf hb near
  obtain ⟨N,np⟩ := C1092MMMPNortheastActualSign.exists_positive p hf hb
  obtain ⟨W,ws,actual,w⟩ := northwest_profile p hf hb near E N ep e np
  have side : 1<W.side := by rw [ws]; exact side_gt p 7
  have same : W.side=N.side := ws.trans ((side_same p 7 6).trans np.side.symm)
  have apart : ∀ x y,¬(W.Inside x y ∧ N.Inside x y) := by
    intro x y own
    exact owners_disjoint p hf 7 6 (by decide) _ _
      ⟨(actual x y).mp own.1,(np.actual x y).mp own.2⟩
  have upper := C1092MMMPUpperThird.upper_third W N side same w.normal w.slope
    w.origin w.marker w.height w.lowerU (northeast_core p hf hb N np) apart
  exact C1092TwoFifths.impossible E N ((owners p 10).translated 2 2)
    (input_of_profiles p hf hb near E N ep.side ep.actual np e upper.le)

/-- Both strict wall points needed by the earlier strong northeast
ending now follow from the original branch, with no auxiliary producer. -/
theorem wall_points (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp) :
    C1092MMMPActualProfile.WallPoints p :=
  ⟨C1092MMMPTopOrigin.point p hf hb,
    C1092MMMPActualProfile.right_reach_of_missing_near p hf hb
      (near_impossible p hf hb)⟩

theorem family_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp) : False :=
  C1092MMMPActualProfile.impossible_of_wall_points p hf hb (wall_points p hf hb)

/-- Original branch index 1, including all side, wall and contact cases. -/
theorem branch_ending : BranchEnding 1 :=
  C1092MMMPActualProfile.branch_of_wall_points wall_points

#print axioms near_impossible
#print axioms family_impossible
#print axioms branch_ending
end N12Compact.C1092MMMPTwoFifthsEntrance
