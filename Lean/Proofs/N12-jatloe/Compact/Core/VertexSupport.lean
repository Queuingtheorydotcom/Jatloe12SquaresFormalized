import Compact.Core.PairSupportFast

/-!
One two-row basis can certify every direction in its positive normal cone.
The intersection coordinates are checked once, independently of direction.
Subsequent support bounds use just cone signs and dot products against this
cached vertex. They do not re-read input memberships or solve a new linear
system. All strictness inherited from active input rows is retained.
-/

set_option Elab.async false

namespace N12Compact.VertexSupport

open IntegerSupport PairSupport

structure Basis where
  first : Row
  second : Row
  x : Int
  y : Int
  denominator : Int
  deriving DecidableEq

def Basis.Check (basis : Basis) : Prop :=
  0 < basis.denominator ∧
  basis.first.x * basis.x + basis.first.y * basis.y +
      basis.first.constant * basis.denominator = 0 ∧
  basis.second.x * basis.x + basis.second.y * basis.y +
      basis.second.constant * basis.denominator = 0

instance (basis : Basis) : Decidable basis.Check :=
  inferInstanceAs (Decidable (_ ∧ _))

def Basis.Cone (basis : Basis) (x y : Int) : Prop :=
  let weights := cramer basis.first basis.second x y
  0 ≤ weights.left ∧ 0 ≤ weights.right ∧ 0 < weights.scale

instance (basis : Basis) (x y : Int) : Decidable (basis.Cone x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Basis.Strict (basis : Basis) (x y : Int) : Prop :=
  let weights := cramer basis.first basis.second x y
  (0 < weights.left ∧ basis.first.strict = true) ∨
    (0 < weights.right ∧ basis.second.strict = true)

instance (basis : Basis) (x y : Int) : Decidable (basis.Strict x y) :=
  inferInstanceAs (Decidable (_ ∨ _))

def Basis.bound (basis : Basis) (x y : Int) : Row :=
  ⟨basis.denominator * x, basis.denominator * y,
    -(x * basis.x + y * basis.y), decide (basis.Strict x y)⟩

def Basis.certificate (basis : Basis) (x y : Int) : TwoRow :=
  let weights := cramer basis.first basis.second x y
  ⟨weights.left * basis.denominator, weights.right * basis.denominator, weights.scale⟩

theorem Basis.certificate_checked (basis : Basis) (checked : basis.Check)
    (x y : Int) (cone : basis.Cone x y) :
    (basis.certificate x y).Check basis.first basis.second (basis.bound x y) := by
  obtain ⟨hd, hv₁, hv₂⟩ := checked
  obtain ⟨hl, hr, hs⟩ := cone
  have hx := cramer_x basis.first basis.second x y
  have hy := cramer_y basis.first basis.second x y
  let weights := cramer basis.first basis.second x y
  have coefficient_x : weights.left * basis.denominator * basis.first.x +
      weights.right * basis.denominator * basis.second.x =
      weights.scale * (basis.denominator * x) := by
    calc
      _ = basis.denominator * (weights.left * basis.first.x +
            weights.right * basis.second.x) := by ring
      _ = _ := by rw [hx]; ring
  have coefficient_y : weights.left * basis.denominator * basis.first.y +
      weights.right * basis.denominator * basis.second.y =
      weights.scale * (basis.denominator * y) := by
    calc
      _ = basis.denominator * (weights.left * basis.first.y +
            weights.right * basis.second.y) := by ring
      _ = _ := by rw [hy]; ring
  have constant : weights.left * basis.denominator * basis.first.constant +
      weights.right * basis.denominator * basis.second.constant =
      weights.scale * -(x * basis.x + y * basis.y) := by
    calc
      _ = weights.left * (basis.first.x * basis.x + basis.first.y * basis.y +
            basis.first.constant * basis.denominator) +
          weights.right * (basis.second.x * basis.x + basis.second.y * basis.y +
            basis.second.constant * basis.denominator) -
          (weights.left * basis.first.x + weights.right * basis.second.x) * basis.x -
          (weights.left * basis.first.y + weights.right * basis.second.y) * basis.y := by ring
      _ = _ := by rw [hv₁, hv₂, hx, hy]; ring
  refine ⟨mul_nonneg hl hd.le, mul_nonneg hr hd.le, hs,
    coefficient_x, coefficient_y, constant, ?_⟩
  intro hstrict
  have h : basis.Strict x y := of_decide_eq_true hstrict
  rcases h with h | h
  · exact Or.inl ⟨mul_pos h.1 hd, h.2⟩
  · exact Or.inr ⟨mul_pos h.1 hd, h.2⟩

/-- The cached vertex yields an exact directional inequality from the two
actual input rows. No geometric optimality assertion is needed. -/
theorem Basis.sound (basis : Basis) (checked : basis.Check) (x y : Int)
    (cone : basis.Cone x y) (p : Fin 2 → ℝ)
    (first : basis.first.Holds p) (second : basis.second.Holds p) :
    (basis.bound x y).Holds p :=
  (basis.certificate_checked checked x y cone).sound p first second

/-- Once two directional bounds have been obtained, pairing them needs only
one exact constant comparison and its strictness test. -/
def PairCheck (a b : Basis) (x y scale constant : Int) : Prop :=
  scale * (b.denominator * (a.bound x y).constant +
      a.denominator * (b.bound (-x) (-y)).constant) ≤
      a.denominator * b.denominator * constant ∧
  (scale * (b.denominator * (a.bound x y).constant +
      a.denominator * (b.bound (-x) (-y)).constant) <
      a.denominator * b.denominator * constant ∨
    (a.bound x y).strict = true ∨ (b.bound (-x) (-y)).strict = true)

instance (a b : Basis) (x y scale constant : Int) :
    Decidable (PairCheck a b x y scale constant) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem pair_sound (a b : Basis) (ha : a.Check) (hb : b.Check)
    (x y scale constant : Int) (hscale : 0 < scale)
    (checked : PairCheck a b x y scale constant) (p q : Fin 2 → ℝ)
    (hp : (a.bound x y).Holds p) (hq : (b.bound (-x) (-y)).Holds q) :
    0 < (Target.mk (scale*x) (scale*y) constant).eval p q := by
  let A := a.bound x y
  let B := b.bound (-x) (-y)
  let w : Weights := ⟨scale*b.denominator,0,scale*a.denominator,0,
    a.denominator*b.denominator⟩
  have wa : 0 < scale*b.denominator := mul_pos hscale hb.1
  have wb : 0 < scale*a.denominator := mul_pos hscale ha.1
  have constant_identity : w.constant A A B B =
      scale * (b.denominator * A.constant + a.denominator * B.constant) := by
    dsimp [w, Weights.constant]
    ring
  have hw : w.Check A A B B ⟨scale*x,scale*y,constant⟩ := by
    refine ⟨wa.le, (show (0 : Int) ≤ 0 from le_rfl),
      wb.le, (show (0 : Int) ≤ 0 from le_rfl), mul_pos ha.1 hb.1,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [w,A,B,Basis.bound]; ring
    · dsimp [w,A,B,Basis.bound]; ring
    · dsimp [w,A,B,Basis.bound]; ring
    · dsimp [w,A,B,Basis.bound]; ring
    · rw [constant_identity]
      exact checked.1
    · rcases checked.2 with slack | strictA | strictB
      · exact Or.inl (by rw [constant_identity]; exact slack)
      · exact Or.inr (Or.inl ⟨wa,strictA⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨wb,strictB⟩)))
  exact hw.sound p q hp hp hq hq

#print axioms Basis.sound
#print axioms pair_sound

end N12Compact.VertexSupport
