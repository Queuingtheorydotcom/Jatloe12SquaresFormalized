import Compact.Completion.C1092.MPPMOnePositiveRetainingClearance
import Compact.Completion.C1092.MPPMAllNonpositivePair

/-! The complete local Lemma 3 after its narrow source profile has
been supplied. The source may obtain that profile from a missing
negative or a positive predecessor, so the same result also serves the
two-positive chapter. All bar/crosspoint inputs retain their real owners. -/
namespace N12Compact.C1092MPPMOnePositive
open S12 S12Pilot C977CornerCubic C1092MPPMAllNonpositive
set_option Elab.async false
noncomputable section

/-- A narrow retaining negative C cannot precede another retaining
negative D when the actual next crosspoint is foreign to D and its
whole following bar belongs to one actual B. No sign of that next owner
is needed. E is the fixed physical clockwise frame of D throughout. -/
theorem retaining_successor_impossible (C D B : OpenSquare)
    (h : RetainingPairInput C (C1092MMMPEndingAxes.clockwise D))
    (core : Core D) (foreign : ¬D.Inside 0 (-1/2))
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(D.Inside x y ∧ B.Inside x y)) : False := by
  have cleared := retaining_successor_cleared C D B h core foreign bar apart
  exact pair_impossible C (C1092MMMPEndingAxes.clockwise D) h.source
    (by linarith only [h.close]) cleared h.same h.marker h.ordinary h.apart

end
#print axioms retaining_successor_impossible
end N12Compact.C1092MPPMOnePositive
