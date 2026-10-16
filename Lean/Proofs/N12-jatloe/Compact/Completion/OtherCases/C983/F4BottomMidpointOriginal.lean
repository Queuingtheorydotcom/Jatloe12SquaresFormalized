import Compact.Completion.OtherCases.C983.ActualBars
import Compact.Completion.OtherCases.C983.F4BottomMidpoint

/-! Actual-owner adapter for the manuscript's direct bottom-midpoint
exclusion. The stronger Q0 seed stays explicit: the historical
S12.MissingCornerBranches route imports the absent SingletonMissingTriangles
module and is not a closed source proof in this checkpoint. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f4_bottom_midpoint_excluded_of_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7)
    (E : OpenSquare) (t : ℝ) (shape : E.side=(owners p 5).side)
    (physical : ∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2))
    (data : F4BottomMidpoint.SoutheastData E t)
    (cornerSeed : (owners p 0).Inside (49/25) (19/25)) :
    ¬(owners p 9).Inside 2 (3/2) := by
  let B := (owners p 9).translated 2 2
  have same : B.side=E.side := (owners_same_side p 9 5).trans shape.symm
  have marker : B.Inside 0 (-543/500) := by
    have h := seed_inside p hf 9 (2,457/500) (by decide +kernel)
    norm_num at h
    dsimp only [B]
    norm_num [inside_translated_iff]
    exact h
  have bar : B.Inside (4/5) (-1) := by
    dsimp only [B]
    norm_num [inside_translated_iff]
    exact bottom_advance p hf
  have westF : (owners p 7).Inside 2 (87/50) := by
    have h := auxiliary_inside p 7 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have missingF : ¬B.Inside 0 (-13/50) := by
    intro own
    have original : (owners p 9).Inside 2 (87/50) := by
      norm_num [B,inside_translated_iff] at own
      exact own
    exact owners_apart p hf 9 7 (by decide +kernel) _ _ ⟨original,westF⟩
  have missingSeed : ¬B.Inside (-1/25) (-31/25) := by
    intro own
    have original : (owners p 9).Inside (49/25) (19/25) := by
      norm_num [B,inside_translated_iff] at own
      exact own
    exact owners_apart p hf 9 0 (by decide +kernel) _ _ ⟨original,cornerSeed⟩
  have disjoint : ∀ x y,¬(B.Inside x y ∧ E.Inside x y) := by
    intro x y own
    exact owners_apart p hf 9 5 (by decide +kernel) (x+2) (y+2)
      ⟨by simpa only [add_comm] using (inside_translated_iff _ 2 2 x y).mp own.1,
        (physical x y).mp own.2⟩
  have excluded := F4BottomMidpoint.excluded B E t same data marker bar missingF missingSeed disjoint
  intro own
  apply excluded
  dsimp only [B]
  norm_num [inside_translated_iff]
  exact own

end
#print axioms f4_bottom_midpoint_excluded_of_frame
end N12Compact.Completion.OtherCases.C983
