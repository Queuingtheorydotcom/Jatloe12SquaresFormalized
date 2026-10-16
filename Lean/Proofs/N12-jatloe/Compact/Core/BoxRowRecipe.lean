import Compact.Core.IntegerSupport

/-! Four axis faces share one geometric box description.  Each bound retains
its exact integer numerator, positive denominator and strictness.  The decoder
reconstructs the original integer affine row; no rounding or rescaling occurs.
-/
namespace N12Compact.BoxRowRecipe
open IntegerSupport

inductive Face where
  | left | right | bottom | top
  deriving DecidableEq, Inhabited

structure Bound where
  numerator : Int
  denominatorPred : Nat
  strict : Bool

def Bound.denominator (b : Bound) : Nat := b.denominatorPred + 1

theorem Bound.positive_denominator (b : Bound) : 0 < b.denominator :=
  Nat.zero_lt_succ _

def Bound.row (b : Bound) : Face → Row × Nat
  | .left => (⟨b.denominator, 0, -b.numerator, b.strict⟩, b.denominatorPred)
  | .right => (⟨-(b.denominator : Int), 0, b.numerator, b.strict⟩, b.denominatorPred)
  | .bottom => (⟨0, b.denominator, -b.numerator, b.strict⟩, b.denominatorPred)
  | .top => (⟨0, -(b.denominator : Int), b.numerator, b.strict⟩, b.denominatorPred)

def Bound.slack (b : Bound) (face : Face) (p : Fin 2 → ℝ) : ℝ :=
  match face with
  | .left => b.denominator * p 0 - b.numerator
  | .right => b.numerator - b.denominator * p 0
  | .bottom => b.denominator * p 1 - b.numerator
  | .top => b.numerator - b.denominator * p 1

def Bound.Holds (b : Bound) (face : Face) (p : Fin 2 → ℝ) : Prop :=
  if b.strict then 0 < b.slack face p else 0 ≤ b.slack face p

theorem Bound.row_eval (b : Bound) (face : Face) (p : Fin 2 → ℝ) :
    (b.row face).1.eval p = b.slack face p := by
  cases face <;> simp [row, Row.eval, slack, sub_eq_add_neg] <;> ring

theorem Bound.row_strict (b : Bound) (face : Face) :
    (b.row face).1.strict = b.strict := by cases face <;> rfl

theorem Bound.row_holds_iff (b : Bound) (face : Face) (p : Fin 2 → ℝ) :
    (b.row face).1.Holds p ↔ b.Holds face p := by
  simp only [Row.Holds, Holds, row_strict, row_eval]

theorem Bound.row_denominator (b : Bound) (face : Face) :
    (b.row face).2 + 1 = b.denominator := by cases face <;> rfl

structure Box where
  left : Bound
  right : Bound
  bottom : Bound
  top : Bound

def Box.bound (b : Box) : Face → Bound
  | .left => b.left
  | .right => b.right
  | .bottom => b.bottom
  | .top => b.top

def Box.Holds (b : Box) (p : Fin 2 → ℝ) : Prop :=
  b.left.Holds .left p ∧ b.right.Holds .right p ∧
    b.bottom.Holds .bottom p ∧ b.top.Holds .top p

theorem Box.rows_holds_iff (b : Box) (p : Fin 2 → ℝ) :
    (∀ face, ((b.bound face).row face).1.Holds p) ↔ b.Holds p := by
  constructor
  · intro h
    exact ⟨(b.left.row_holds_iff .left p).mp (h .left),
      (b.right.row_holds_iff .right p).mp (h .right),
      (b.bottom.row_holds_iff .bottom p).mp (h .bottom),
      (b.top.row_holds_iff .top p).mp (h .top)⟩
  · intro h face
    rcases h with ⟨hl, hr, hb, ht⟩
    cases face
    · exact (b.left.row_holds_iff .left p).mpr hl
    · exact (b.right.row_holds_iff .right p).mpr hr
    · exact (b.bottom.row_holds_iff .bottom p).mpr hb
    · exact (b.top.row_holds_iff .top p).mpr ht

end N12Compact.BoxRowRecipe
