import Compact.Core.SparseInteger
import Compact.Core.PairSupport
import Mathlib.Tactic.FinCases

/-!
# Two-index affine support with exact integer slack

For a planar target inequality, two source-row indices determine the Cramer
weights. Any nonnegative constant slack is supplied by the true row `1 > 0`.
The sparse integer checker independently checks all signs, identities and
strictness. Thus determinant synthesis is data preparation, not a proof rule.
-/

namespace N12Compact.RowSupport

open IntegerSupport SparseInteger

def one : Row := ⟨0, 0, 1, true⟩

theorem one_holds (p : Fin 2 → ℝ) : one.Holds p := by
  norm_num [one, Row.Holds, Row.eval]

def sourceRows (a b : Row) : Fin 3 → Row := ![a, b, one]

def certificate (a b target : Row) : Certificate 3 :=
  let weights := PairSupport.cramer a b target.x target.y
  let slack := weights.scale * target.constant -
    weights.left * a.constant - weights.right * b.constant
  ⟨[(weights.left, 0), (weights.right, 1), (slack, 2)], weights.scale⟩

def Check (a b target : Row) : Prop :=
  (certificate a b target).Check (sourceRows a b) target

instance (a b target : Row) : Decidable (Check a b target) :=
  inferInstanceAs (Decidable (Certificate.Check _ _ _))

theorem sound {a b target : Row} (checked : Check a b target)
    (p : Fin 2 → ℝ) (ha : a.Holds p) (hb : b.Holds p) : target.Holds p := by
  have sources : ∀ i : Fin 3, (sourceRows a b i).Holds p := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact one_holds p
  exact checked.sound p (fun term _ => sources term.2)

theorem normalized_sound {a b target : Row} (checked : Check a b target)
    (da db dt : Nat) (hda : 0 < da) (hdb : 0 < db) (hdt : 0 < dt)
    (p : Fin 2 → ℝ) (ha : (a.normalized da).Holds p)
    (hb : (b.normalized db).Holds p) : (target.normalized dt).Holds p := by
  apply (target.normalized_holds_iff dt hdt p).mpr
  exact sound checked p ((a.normalized_holds_iff da hda p).mp ha)
    ((b.normalized_holds_iff db hdb p).mp hb)

#print axioms normalized_sound

end N12Compact.RowSupport
