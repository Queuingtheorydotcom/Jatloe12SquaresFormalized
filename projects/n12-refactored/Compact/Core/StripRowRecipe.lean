import Compact.Core.BoxRowRecipe

/-! Opposite parallel faces share one linear form. The two positive integer
scales retain the original coefficient normalization; strict endpoints and
the original normalized-row denominators are preserved separately. -/
namespace N12Compact.StripRowRecipe
open IntegerSupport BoxRowRecipe

inductive Face where
  | lower
  | upper
  deriving DecidableEq, Inhabited

structure Strip where
  x : Int
  y : Int
  lowerScalePred : Nat
  upperScalePred : Nat
  lower : Bound
  upper : Bound

def Strip.lowerScale (s : Strip) : Nat := s.lowerScalePred + 1
def Strip.upperScale (s : Strip) : Nat := s.upperScalePred + 1

theorem Strip.lowerScale_pos (s : Strip) : 0 < s.lowerScale := Nat.zero_lt_succ _
theorem Strip.upperScale_pos (s : Strip) : 0 < s.upperScale := Nat.zero_lt_succ _

def Strip.linear (s : Strip) (p : Fin 2 → ℝ) : ℝ := s.x * p 0 + s.y * p 1

def Strip.row (s : Strip) : Face → Row × Nat
  | .lower => (⟨s.lowerScale * s.x, s.lowerScale * s.y,
      -s.lower.numerator, s.lower.strict⟩, s.lower.denominatorPred)
  | .upper => (⟨-(s.upperScale * s.x), -(s.upperScale * s.y),
      s.upper.numerator, s.upper.strict⟩, s.upper.denominatorPred)

def Strip.slack (s : Strip) (face : Face) (p : Fin 2 → ℝ) : ℝ :=
  match face with
  | .lower => s.lowerScale * s.linear p - s.lower.numerator
  | .upper => s.upper.numerator - s.upperScale * s.linear p

def Strip.bound (s : Strip) : Face → Bound
  | .lower => s.lower
  | .upper => s.upper

def Strip.Holds (s : Strip) (p : Fin 2 → ℝ) : Prop :=
  (if s.lower.strict then 0 < s.slack .lower p else 0 ≤ s.slack .lower p) ∧
  (if s.upper.strict then 0 < s.slack .upper p else 0 ≤ s.slack .upper p)

theorem Strip.row_eval (s : Strip) (face : Face) (p : Fin 2 → ℝ) :
    (s.row face).1.eval p = s.slack face p := by
  cases face <;> simp [row, Row.eval, slack, linear] <;> ring

theorem Strip.row_strict (s : Strip) (face : Face) :
    (s.row face).1.strict = (s.bound face).strict := by cases face <;> rfl

theorem Strip.row_denominator (s : Strip) (face : Face) :
    (s.row face).2 + 1 = (s.bound face).denominator := by cases face <;> rfl

theorem Strip.rows_holds_iff (s : Strip) (p : Fin 2 → ℝ) :
    ((s.row .lower).1.Holds p ∧ (s.row .upper).1.Holds p) ↔ s.Holds p := by
  simp only [Row.Holds, row_strict, row_eval, bound, Holds]

end N12Compact.StripRowRecipe
