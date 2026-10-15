import Compact.Core.IntegerSupport

/-!
The authentic C696 source-pose-0 / target-row-802 implication used in
C696SupportFixture, now checked with integers only. Its original denominators
remain explicit in the final theorem. No rational decision computation occurs
in the certificate check, and this module does not import the rational fixture.
-/

namespace N12Compact.IntegerSupportCase

open IntegerSupport

def left : Row := ⟨7426250000, -475275000000, 537911935887, false⟩
def right : Row := ⟨40033643750000, -2780475000000, -56838381160977, false⟩
def target : Row := ⟨58683525000000, -4075775000000, -83316835326773, false⟩

/-- The primitive integer relation after clearing denominators and removing
the common gcd. These 7/12/12-digit weights replace the rational weights. -/
def certificate : TwoRow := ⟨1605785, 891537427849, 608202928986⟩

theorem checked : certificate.Check left right target := by decide +kernel

/-- Exact original-model implication, with the authentic positive denominators.
Only the two source inequalities contributing to the target are required. -/
theorem original_implication (p : Fin 2 → ℝ)
    (ha : (left.normalized 475275000000).Holds p)
    (hb : (right.normalized 40033643750000).Holds p) :
    (target.normalized 58683525000000).Holds p :=
  checked.normalized_sound 475275000000 40033643750000 58683525000000
    (by decide) (by decide) (by decide) p ha hb

#print axioms checked
#print axioms original_implication

end N12Compact.IntegerSupportCase
