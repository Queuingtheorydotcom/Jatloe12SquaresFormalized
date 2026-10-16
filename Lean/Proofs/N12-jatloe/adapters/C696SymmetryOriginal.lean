import Compact.Geometry.C696Symmetry
import Completion.Cases.C696.RootZeroSymmetry

/-!
Adapter to the unchanged original normalized-packing and owner definitions.
This source is separate from the default compact core because its historical
imports are not restored in the sparse local checkout. It must be checked
against the original pinned project before claiming a packing-level result.
-/
namespace N12Compact.C696Symmetry.Original

open S12 S12Pilot
open S12Completion.C696.SideSignPacking
open S12Completion.C696.CornerReduction
open S12Completion.C696.RootZeroSymmetry

noncomputable def rootZeroSwap : HeightSwap NormalizedPacking where
  valid p := codedMarkerFamily p = family ∧ CornerRoot p 0
  bottom p := centerY (owners p 9)
  top p := centerY (owners p 11)
  turn p := halfTurn.pullPacking p
  preserves p hp := ⟨halfTurn_packing_family p hp.1,
    halfTurn_root_zero p hp.1 hp.2⟩
  bottom_turn p hp := by
    simpa [ownerHalfTurn] using halfTurn_owner_centerY p hp.1 9
  top_turn p hp := by
    simpa [ownerHalfTurn] using halfTurn_owner_centerY p hp.1 11

/-- Every original root-zero counterexample has a physical representative
with the additional coupled center inequality. -/
theorem root_zero_joint_normal_form (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (hr : CornerRoot p 0) :
    ∃ q : NormalizedPacking,
      (q = p ∨ q = halfTurn.pullPacking p) ∧
      codedMarkerFamily q = family ∧ CornerRoot q 0 ∧
      centerY (owners q 9) + centerY (owners q 11) ≤ 4 := by
  obtain ⟨q, orbit, hq, joint⟩ :=
    joint_normal_form rootZeroSwap p ⟨hf, hr⟩
  exact ⟨q, orbit, hq.1, hq.2, joint⟩

#print axioms root_zero_joint_normal_form

end N12Compact.C696Symmetry.Original
