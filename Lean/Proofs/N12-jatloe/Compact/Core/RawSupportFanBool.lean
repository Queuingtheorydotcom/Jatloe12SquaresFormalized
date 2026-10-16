import Compact.Core.RawSupportFanBridge

/-! Optional ordinary-kernel Boolean replay for the same eight-axis predicate.

Cramer weights and the scalar pair comparison are computed once per axis.
The Boolean loop has eight explicit axes and contains no `Decidable` evidence
for a quantified proposition. `check_sound` proves the exact existing raw
checker. A numeric batch may prove `check ... = true` by `rfl`; no native
evaluation, external result, or new trusted proof mechanism is used.
-/

set_option Elab.async false

namespace N12Compact.RawSupportFanBool
open IntegerSupport ReferenceAxis PairPruning RawSupportFan PairSupport

def cone (weights : TwoRow) : Bool :=
  decide (0 ≤ weights.left) &&
    (decide (0 ≤ weights.right) && decide (0 < weights.scale))

def strict (weights : TwoRow) (a b : Row) : Bool :=
  (decide (0 < weights.left) && a.strict) ||
    (decide (0 < weights.right) && b.strict)

def axisCheck (a b : VertexSupport.Basis) (x y scale constant : Int) : Bool :=
  let aw := cramer a.first a.second x y
  let bw := cramer b.first b.second (-x) (-y)
  let ac := -(x * a.x + y * a.y)
  let bc := -((-x) * b.x + (-y) * b.y)
  let lhs := scale * (b.denominator * ac + a.denominator * bc)
  let rhs := a.denominator * b.denominator * constant
  cone aw && (cone bw &&
    (decide (lhs ≤ rhs) &&
      (decide (lhs < rhs) || (strict aw a.first a.second || strict bw b.first b.second))))

theorem axisCheck_iff (a b : VertexSupport.Basis) (x y scale constant : Int) :
    axisCheck a b x y scale constant = true ↔
      a.Cone x y ∧ b.Cone (-x) (-y) ∧
        VertexSupport.PairCheck a b x y scale constant := by
  have strict_a : (a.bound x y).strict = true ↔ a.Strict x y := by
    exact decide_eq_true_iff
  have strict_b : (b.bound (-x) (-y)).strict = true ↔ b.Strict (-x) (-y) := by
    exact decide_eq_true_iff
  simp only [VertexSupport.PairCheck, strict_a, strict_b]
  simp only [axisCheck, cone, strict, VertexSupport.Basis.Cone,
    VertexSupport.Basis.bound, VertexSupport.Basis.Strict,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

def axis (a b : Context) (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (i : Fin 8) : Bool :=
  let n := direction a.reference b.reference i
  let A := (a.select (keys i)).basis
  let B := (b.select (opposite (keys i))).basis
  axisCheck A B n.x n.y (CachedSupportFan.scale a.reference b.reference)
    (target a.reference b.reference n).constant

def check (a b : Context) (keys : Fin 8 → Nat) (opposite : Nat → Nat) : Bool :=
  axis a b keys opposite 0 &&
  (axis a b keys opposite 1 &&
  (axis a b keys opposite 2 &&
  (axis a b keys opposite 3 &&
  (axis a b keys opposite 4 &&
  (axis a b keys opposite 5 &&
  (axis a b keys opposite 6 && axis a b keys opposite 7))))))

theorem check_sound (a b : Context) (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : check a b keys opposite = true) : PairCheck a b keys opposite := by
  simp only [check, Bool.and_eq_true] at checked
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  have current : axis a b keys opposite i = true := by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact checked.1
    · exact checked.2.1
    · exact checked.2.2.1
    · exact checked.2.2.2.1
    · exact checked.2.2.2.2.1
    · exact checked.2.2.2.2.2.1
    · exact checked.2.2.2.2.2.2.1
    · exact checked.2.2.2.2.2.2.2
  exact (axisCheck_iff _ _ _ _ _ _).mp current

end N12Compact.RawSupportFanBool

#print axioms N12Compact.RawSupportFanBool.check_sound
