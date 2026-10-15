import Compact.Core.IntegerSupport

/-!
Integer support certificates for two independent plane points.

Each strict separation-axis inequality cites just two rows for each point.
Two exact 2×2 determinants reconstruct the weights. The checker verifies
the resulting identity, signs and strictness; the determinant implementation
does not belong to the logical trust boundary. Every cited row remains an
explicit hypothesis. No finite sampling or geometric assumption is added.
-/

namespace N12Compact.PairSupport

open IntegerSupport S12

structure Target where
  x : Int
  y : Int
  constant : Int
  deriving DecidableEq

def Target.eval (t : Target) (p q : Fin 2 → ℝ) : ℝ :=
  (t.x : ℝ) * (p 0 - q 0) + (t.y : ℝ) * (p 1 - q 1) + t.constant

def Target.normalized (t : Target) (den : Nat) : LinearConstraint 4 :=
  ⟨⟨![(t.x : ℚ) / den, (t.y : ℚ) / den,
       -(t.x : ℚ) / den, -(t.y : ℚ) / den], (t.constant : ℚ) / den⟩, true⟩

theorem Target.normalized_holds_iff (t : Target) (den : Nat)
    (positive : 0 < den) (p q : Fin 2 → ℝ) :
    (t.normalized den).Holds ![p 0, p 1, q 0, q 1] ↔ 0 < t.eval p q := by
  have hd : (0 : ℝ) < den := by exact_mod_cast positive
  have eval_eq : (t.normalized den).form.eval ![p 0, p 1, q 0, q 1] =
      t.eval p q / den := by
    simp [Target.normalized, Affine.eval, Target.eval, Fin.sum_univ_succ,
      div_eq_mul_inv] <;> ring
  change (0 < (t.normalized den).form.eval ![p 0, p 1, q 0, q 1]) ↔ _
  rw [eval_eq]
  exact div_pos_iff_of_pos_right hd

structure Weights where
  a₁ : Int
  a₂ : Int
  b₁ : Int
  b₂ : Int
  scale : Int
  deriving DecidableEq

def Weights.constant (w : Weights) (a₁ a₂ b₁ b₂ : Row) : Int :=
  w.a₁ * a₁.constant + w.a₂ * a₂.constant +
    w.b₁ * b₁.constant + w.b₂ * b₂.constant

def Weights.Check (w : Weights) (a₁ a₂ b₁ b₂ : Row) (t : Target) : Prop :=
  0 ≤ w.a₁ ∧ 0 ≤ w.a₂ ∧ 0 ≤ w.b₁ ∧ 0 ≤ w.b₂ ∧ 0 < w.scale ∧
  w.a₁ * a₁.x + w.a₂ * a₂.x = w.scale * t.x ∧
  w.a₁ * a₁.y + w.a₂ * a₂.y = w.scale * t.y ∧
  w.b₁ * b₁.x + w.b₂ * b₂.x = -(w.scale * t.x) ∧
  w.b₁ * b₁.y + w.b₂ * b₂.y = -(w.scale * t.y) ∧
  w.constant a₁ a₂ b₁ b₂ ≤ w.scale * t.constant ∧
  (w.constant a₁ a₂ b₁ b₂ < w.scale * t.constant ∨
    (0 < w.a₁ ∧ a₁.strict = true) ∨ (0 < w.a₂ ∧ a₂.strict = true) ∨
    (0 < w.b₁ ∧ b₁.strict = true) ∨ (0 < w.b₂ ∧ b₂.strict = true))

instance (w : Weights) (a₁ a₂ b₁ b₂ : Row) (t : Target) :
    Decidable (w.Check a₁ a₂ b₁ b₂ t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Weights.Check.sound {w : Weights} {a₁ a₂ b₁ b₂ : Row} {t : Target}
    (checked : w.Check a₁ a₂ b₁ b₂ t) (p q : Fin 2 → ℝ)
    (ha₁ : a₁.Holds p) (ha₂ : a₂.Holds p)
    (hb₁ : b₁.Holds q) (hb₂ : b₂.Holds q) : 0 < t.eval p q := by
  obtain ⟨wa₁, wa₂, wb₁, wb₂, ws, ax, ay, bx, byy, constant, strict⟩ := checked
  have wa₁' : (0 : ℝ) ≤ w.a₁ := by exact_mod_cast wa₁
  have wa₂' : (0 : ℝ) ≤ w.a₂ := by exact_mod_cast wa₂
  have wb₁' : (0 : ℝ) ≤ w.b₁ := by exact_mod_cast wb₁
  have wb₂' : (0 : ℝ) ≤ w.b₂ := by exact_mod_cast wb₂
  have ws' : (0 : ℝ) < w.scale := by exact_mod_cast ws
  have ax' : (w.a₁ : ℝ) * a₁.x + (w.a₂ : ℝ) * a₂.x =
      (w.scale : ℝ) * t.x := by exact_mod_cast ax
  have ay' : (w.a₁ : ℝ) * a₁.y + (w.a₂ : ℝ) * a₂.y =
      (w.scale : ℝ) * t.y := by exact_mod_cast ay
  have bx' : (w.b₁ : ℝ) * b₁.x + (w.b₂ : ℝ) * b₂.x =
      -((w.scale : ℝ) * t.x) := by exact_mod_cast bx
  have by' : (w.b₁ : ℝ) * b₁.y + (w.b₂ : ℝ) * b₂.y =
      -((w.scale : ℝ) * t.y) := by exact_mod_cast byy
  have hc : (w.constant a₁ a₂ b₁ b₂ : ℝ) ≤ (w.scale : ℝ) * t.constant := by
    exact_mod_cast constant
  have identity : (w.a₁ : ℝ) * a₁.eval p + (w.a₂ : ℝ) * a₂.eval p +
      (w.b₁ : ℝ) * b₁.eval q + (w.b₂ : ℝ) * b₂.eval q +
      ((w.scale : ℝ) * t.constant - w.constant a₁ a₂ b₁ b₂) =
      (w.scale : ℝ) * t.eval p q := by
    calc
      _ = ((w.a₁ : ℝ) * a₁.x + (w.a₂ : ℝ) * a₂.x) * p 0 +
          ((w.a₁ : ℝ) * a₁.y + (w.a₂ : ℝ) * a₂.y) * p 1 +
          ((w.b₁ : ℝ) * b₁.x + (w.b₂ : ℝ) * b₂.x) * q 0 +
          ((w.b₁ : ℝ) * b₁.y + (w.b₂ : ℝ) * b₂.y) * q 1 +
          (w.scale : ℝ) * t.constant := by
            simp only [Row.eval, Weights.constant, Int.cast_add, Int.cast_mul]
            ring
      _ = _ := by rw [ax', ay', bx', by']; dsimp [Target.eval]; ring
  have h₁ := mul_nonneg wa₁' (a₁.nonneg p ha₁)
  have h₂ := mul_nonneg wa₂' (a₂.nonneg p ha₂)
  have h₃ := mul_nonneg wb₁' (b₁.nonneg q hb₁)
  have h₄ := mul_nonneg wb₂' (b₂.nonneg q hb₂)
  have positive : 0 < (w.scale : ℝ) * t.eval p q := by
    rcases strict with hs | hs | hs | hs | hs
    · have hs' : (w.constant a₁ a₂ b₁ b₂ : ℝ) <
          (w.scale : ℝ) * t.constant := by exact_mod_cast hs
      linarith
    · have hp : (0 : ℝ) < w.a₁ := by exact_mod_cast hs.1
      have := mul_pos hp (a₁.positive p hs.2 ha₁)
      linarith
    · have hp : (0 : ℝ) < w.a₂ := by exact_mod_cast hs.1
      have := mul_pos hp (a₂.positive p hs.2 ha₂)
      linarith
    · have hp : (0 : ℝ) < w.b₁ := by exact_mod_cast hs.1
      have := mul_pos hp (b₁.positive q hs.2 hb₁)
      linarith
    · have hp : (0 : ℝ) < w.b₂ := by exact_mod_cast hs.1
      have := mul_pos hp (b₂.positive q hs.2 hb₂)
      linarith
  exact (mul_lt_mul_left ws').mp (by simpa only [mul_zero] using positive)

/-- Cramer synthesis has no unchecked correctness obligation: `Check` below
verifies its complete output before the soundness theorem can be used. -/
def cramer (a b : Row) (x y : Int) : TwoRow :=
  let det := a.x * b.y - a.y * b.x
  let sign : Int := if 0 ≤ det then 1 else -1
  ⟨sign * (x * b.y - y * b.x), sign * (a.x * y - a.y * x), sign * det⟩

def synthesize (a₁ a₂ b₁ b₂ : Row) (t : Target) : Weights :=
  let a := cramer a₁ a₂ t.x t.y
  let b := cramer b₁ b₂ (-t.x) (-t.y)
  ⟨a.left * b.scale, a.right * b.scale,
    b.left * a.scale, b.right * a.scale, a.scale * b.scale⟩

def Check (a₁ a₂ b₁ b₂ : Row) (t : Target) : Prop :=
  (synthesize a₁ a₂ b₁ b₂ t).Check a₁ a₂ b₁ b₂ t

instance (a₁ a₂ b₁ b₂ : Row) (t : Target) : Decidable (Check a₁ a₂ b₁ b₂ t) :=
  inferInstanceAs (Decidable (Weights.Check _ _ _ _ _ _))

theorem sound {a₁ a₂ b₁ b₂ : Row} {t : Target}
    (checked : Check a₁ a₂ b₁ b₂ t) (p q : Fin 2 → ℝ)
    (ha₁ : a₁.Holds p) (ha₂ : a₂.Holds p)
    (hb₁ : b₁.Holds q) (hb₂ : b₂.Holds q) : 0 < t.eval p q :=
  checked.sound p q ha₁ ha₂ hb₁ hb₂

theorem normalized_sound {a₁ a₂ b₁ b₂ : Row} {t : Target}
    (checked : Check a₁ a₂ b₁ b₂ t) (da₁ da₂ db₁ db₂ dt : Nat)
    (hda₁ : 0 < da₁) (hda₂ : 0 < da₂) (hdb₁ : 0 < db₁) (hdb₂ : 0 < db₂)
    (hdt : 0 < dt) (p q : Fin 2 → ℝ)
    (ha₁ : (a₁.normalized da₁).Holds p) (ha₂ : (a₂.normalized da₂).Holds p)
    (hb₁ : (b₁.normalized db₁).Holds q) (hb₂ : (b₂.normalized db₂).Holds q) :
    (t.normalized dt).Holds ![p 0, p 1, q 0, q 1] := by
  apply (t.normalized_holds_iff dt hdt p q).mpr
  exact sound checked p q
    ((a₁.normalized_holds_iff da₁ hda₁ p).mp ha₁)
    ((a₂.normalized_holds_iff da₂ hda₂ p).mp ha₂)
    ((b₁.normalized_holds_iff db₁ hdb₁ q).mp hb₁)
    ((b₂.normalized_holds_iff db₂ hdb₂ q).mp hb₂)

#print axioms normalized_sound

end N12Compact.PairSupport
