import Compact.Core.DirectionalSupportCache

/-! A shared point proves overlap using only each reference's own four faces.
The finite checker contains integer arithmetic and exact cone tests. Equality
in a point bound is accepted only when the supporting row is actually strict.
No relative-frame axes or convex-hull coverage are assumed. -/

set_option Elab.async false

namespace N12Compact.CommonPoint
open S12 S12Pilot IntegerSupport ReferenceAxis DirectionalSupportCache RawSupportFan

structure Point where
  x : Int
  y : Int
  denominator : Nat
  deriving DecidableEq

noncomputable def Point.value (point : Point) : ℝ × ℝ :=
  ((point.x : ℝ) / point.denominator, (point.y : ℝ) / point.denominator)

def ownDirection (reference : Reference) (i : Fin 4) : Int × Int :=
  ![(reference.c, reference.s), (-reference.c, -reference.s),
    (-reference.s, reference.c), (reference.s, -reference.c)] i

def datumRow (datum : Datum) : Row :=
  ⟨datum.denominator * datum.x, datum.denominator * datum.y,
    datum.constant, datum.strict⟩

theorem datum_holds (datum : Datum) (context : Context) (key : Nat)
    (P : (Fin 2 → ℝ) → Prop) (valid : context.ValidFor P)
    (checked : datum.Check context key) (center : Fin 2 → ℝ) (holds : P center) :
    (datumRow datum).Holds center := by
  have selected := context.select_valid P valid key
  have bound := VertexSupport.Basis.sound _ selected.1 datum.x datum.y checked.1
    center (selected.2 center holds).1 (selected.2 center holds).2
  simpa only [datumRow, VertexSupport.Basis.bound,
    checked.2.1, checked.2.2.1, checked.2.2.2] using bound

/-- The halfwidth in the unnormalized own direction is den * side / (2*sideDen).
This avoids computing a general-direction radius for the four own faces. -/
def axis (point : Point) (reference : Reference) (datum : Datum) (x y : Int) : Bool :=
  let lhs := 2 * (reference.sideDenominator : Int) *
    (datum.denominator * (x * point.x + y * point.y) +
      datum.constant * point.denominator)
  let rhs := datum.denominator * point.denominator * reference.denominator * reference.side
  decide (0 < point.denominator) && (decide (0 < datum.denominator) &&
    (decide (datum.x = x) && (decide (datum.y = y) &&
      (decide (lhs ≤ rhs) && (decide (lhs < rhs) || datum.strict)))))

private theorem scalar_bound (D E K R x y X Y px py C : ℝ)
    (hD : 0 < D) (hE : 0 < E) (hK : 0 < K)
    (lower : 0 ≤ D * (x * X + y * Y) + C)
    (upper : K * (D * (x * px + y * py) + C * E) ≤ D * E * R)
    (strict : K * (D * (x * px + y * py) + C * E) < D * E * R ∨
      0 < D * (x * X + y * Y) + C) :
    x * (px / E - X) + y * (py / E - Y) < R / K := by
  let gap := R / K - (x * (px / E - X) + y * (py / E - Y))
  have identity : D * E * K * gap =
      (D * E * R - K * (D * (x * px + y * py) + C * E)) +
        E * K * (D * (x * X + y * Y) + C) := by
    dsimp [gap]
    field_simp [ne_of_gt hE, ne_of_gt hK]
    <;> ring
  have positive : 0 < D * E * K * gap := by
    rw [identity]
    rcases strict with slack | strong
    · exact add_pos_of_pos_of_nonneg (sub_pos.mpr slack)
        (mul_nonneg (mul_pos hE hK).le lower)
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr upper)
        (mul_pos (mul_pos hE hK) strong)
  have gap_positive : 0 < gap :=
    (mul_pos_iff_of_pos_left (mul_pos (mul_pos hD hE) hK)).mp positive
  exact sub_pos.mp gap_positive

theorem axis_sound (point : Point) (reference : Reference) (datum : Datum)
    (x y : Int) (valid : reference.Valid) (center : Fin 2 → ℝ)
    (holds : (datumRow datum).Holds center)
    (checked : axis point reference datum x y = true) :
    (x : ℝ) / reference.denominator * (point.value.1 - center 0) +
      (y : ℝ) / reference.denominator * (point.value.2 - center 1) <
        ((reference.side : ℝ) / reference.sideDenominator) / 2 := by
  simp only [axis, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at checked
  obtain ⟨hp, hd, hx, hy, upper, strict⟩ := checked
  have nonneg := Row.nonneg (datumRow datum) center holds
  have lower : 0 ≤ (datum.denominator : ℝ) *
      ((x : ℝ) * center 0 + (y : ℝ) * center 1) + datum.constant := by
    simpa only [datumRow, Row.eval, hx, hy, Int.cast_mul, mul_add, mul_assoc] using nonneg
  have strict' :
      (2 * (reference.sideDenominator : ℝ)) *
        ((datum.denominator : ℝ) * ((x : ℝ) * point.x + (y : ℝ) * point.y) +
          (datum.constant : ℝ) * point.denominator) <
        (datum.denominator : ℝ) * point.denominator *
          (reference.denominator : ℝ) * reference.side ∨
      0 < (datum.denominator : ℝ) *
        ((x : ℝ) * center 0 + (y : ℝ) * center 1) + datum.constant := by
    rcases strict with slack | strong
    · left
      have h := slack
      exact_mod_cast h
    · right
      have h := Row.positive (datumRow datum) center strong holds
      simpa only [datumRow, Row.eval, hx, hy, Int.cast_mul, mul_add, mul_assoc] using h
  have bound := scalar_bound (datum.denominator : ℝ) point.denominator
    (2 * (reference.sideDenominator : ℝ))
    ((reference.denominator : ℝ) * reference.side)
    x y (center 0) (center 1) point.x point.y datum.constant
    (by exact_mod_cast hd) (by exact_mod_cast hp)
    (mul_pos (by norm_num) (by exact_mod_cast valid.2)) lower
    (by
      have upper' :
          (2 * (reference.sideDenominator : ℝ)) *
            ((datum.denominator : ℝ) * ((x : ℝ) * point.x + (y : ℝ) * point.y) +
              (datum.constant : ℝ) * point.denominator) ≤
            (datum.denominator : ℝ) * point.denominator *
              (reference.denominator : ℝ) * reference.side := by exact_mod_cast upper
      simpa only [mul_assoc] using upper')
    (by simpa only [mul_assoc] using strict')
  have hden : (0 : ℝ) < reference.denominator := by exact_mod_cast valid.1
  change (x : ℝ) / reference.denominator * ((point.x : ℝ) / point.denominator - center 0) +
    (y : ℝ) / reference.denominator * ((point.y : ℝ) / point.denominator - center 1) < _
  have rearrange :
      (x : ℝ) / reference.denominator * ((point.x : ℝ) / point.denominator - center 0) +
        (y : ℝ) / reference.denominator * ((point.y : ℝ) / point.denominator - center 1) =
      ((x : ℝ) * ((point.x : ℝ) / point.denominator - center 0) +
        (y : ℝ) * ((point.y : ℝ) / point.denominator - center 1)) / reference.denominator := by ring
  rw [rearrange, div_lt_iff₀ hden]
  calc
    _ < ((reference.denominator : ℝ) * reference.side) /
        (2 * reference.sideDenominator) := bound
    _ = ((reference.side : ℝ) / reference.sideDenominator / 2) * reference.denominator := by ring

theorem inside_of_datums (point : Point) (context : Context) (keys : Fin 4 → Nat)
    (data : Fin 4 → Datum) (P : (Fin 2 → ℝ) → Prop)
    (valid : context.ValidFor P) (reference_valid : context.reference.Valid)
    (reference_checked : context.reference.value.Check)
    (data_checked : ∀ i, (data i).Check context (keys i))
    (checked : ∀ i, axis point context.reference (data i)
      (ownDirection context.reference i).1 (ownDirection context.reference i).2 = true)
    (center : Fin 2 → ℝ) (holds : P center) :
    point.value - (center 0, center 1) ∈
      squareSet (context.reference.value.toSquare reference_checked) := by
  have bounds (i : Fin 4) := axis_sound point context.reference (data i)
    (ownDirection context.reference i).1 (ownDirection context.reference i).2
    reference_valid center (datum_holds _ _ _ P valid (data_checked i) center holds) (checked i)
  have h0 := bounds 0
  have h1 := bounds 1
  have h2 := bounds 2
  have h3 := bounds 3
  simp only [ownDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_succ, Int.cast_neg, neg_div, neg_mul] at h0 h1 h2 h3
  change (context.reference.value.toSquare reference_checked).Inside _ _
  change InBands (-(context.reference.value.side : ℝ) / 2)
    (-(context.reference.value.side : ℝ) / 2) context.reference.value.side
    ((context.reference.value.c : ℝ) * (point.value.1 - center 0) +
      (context.reference.value.s : ℝ) * (point.value.2 - center 1))
    (-(context.reference.value.s : ℝ) * (point.value.1 - center 0) +
      (context.reference.value.c : ℝ) * (point.value.2 - center 1))
  dsimp only [Reference.value, ReferenceSquare.toSquare, S12Pilot.OpenSquare.Inside,
    S12Pilot.InBands]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [h0, h1, h2, h3]

def all4 (f : Fin 4 → Bool) : Bool := f 0 && (f 1 && (f 2 && f 3))

theorem all4_sound (f : Fin 4 → Bool) (checked : all4 f = true) (i : Fin 4) :
    f i = true := by
  simp only [all4, Bool.and_eq_true] at checked
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · exact checked.1
  · exact checked.2.1
  · exact checked.2.2.1
  · exact checked.2.2.2

def check (context : Context) (keys : Fin 4 → Nat) (point : Point) : Bool :=
  all4 fun i =>
    let n := ownDirection context.reference i
    let basis := (context.select (keys i)).basis
    decide (basis.Cone n.1 n.2) &&
      axis point context.reference (Datum.ofBasis basis n.1 n.2) n.1 n.2

theorem inside_sound (context : Context) (keys : Fin 4 → Nat) (point : Point)
    (P : (Fin 2 → ℝ) → Prop) (valid : context.ValidFor P)
    (reference_valid : context.reference.Valid) (reference_checked : context.reference.value.Check)
    (checked : check context keys point = true) (center : Fin 2 → ℝ) (holds : P center) :
    point.value - (center 0, center 1) ∈
      squareSet (context.reference.value.toSquare reference_checked) := by
  let data (i : Fin 4) := Datum.ofBasis (context.select (keys i)).basis
    (ownDirection context.reference i).1 (ownDirection context.reference i).2
  have each (i : Fin 4) := all4_sound _ checked i
  apply inside_of_datums point context keys data P valid reference_valid reference_checked
    (center := center) (holds := holds)
  · intro i
    have hi := each i
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact ⟨hi.1, rfl, rfl, rfl⟩
  · intro i
    have hi := each i
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    exact hi.2

end N12Compact.CommonPoint

#print axioms N12Compact.CommonPoint.inside_sound
