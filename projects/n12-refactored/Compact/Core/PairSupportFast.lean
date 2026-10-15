import Compact.Core.PairSupport

/-!
The two Cramer coefficient identities are polynomial identities, independent
of the certificate data. Prove them once; finite certificates need only check
signs, the constant bound and strictness. This does not alter the targets.
-/

set_option Elab.async false

namespace N12Compact.PairSupport

open IntegerSupport

theorem cramer_x (a b : Row) (x y : Int) :
    (cramer a b x y).left * a.x + (cramer a b x y).right * b.x =
      (cramer a b x y).scale * x := by
  dsimp [cramer]
  ring

theorem cramer_y (a b : Row) (x y : Int) :
    (cramer a b x y).left * a.y + (cramer a b x y).right * b.y =
      (cramer a b x y).scale * y := by
  dsimp [cramer]
  ring

theorem synthesize_ax (a₁ a₂ b₁ b₂ : Row) (t : Target) :
    (synthesize a₁ a₂ b₁ b₂ t).a₁ * a₁.x +
      (synthesize a₁ a₂ b₁ b₂ t).a₂ * a₂.x =
      (synthesize a₁ a₂ b₁ b₂ t).scale * t.x := by
  dsimp [synthesize]
  calc
    _ = ((cramer a₁ a₂ t.x t.y).left * a₁.x +
        (cramer a₁ a₂ t.x t.y).right * a₂.x) *
        (cramer b₁ b₂ (-t.x) (-t.y)).scale := by ring
    _ = _ := by rw [cramer_x]; ring

theorem synthesize_ay (a₁ a₂ b₁ b₂ : Row) (t : Target) :
    (synthesize a₁ a₂ b₁ b₂ t).a₁ * a₁.y +
      (synthesize a₁ a₂ b₁ b₂ t).a₂ * a₂.y =
      (synthesize a₁ a₂ b₁ b₂ t).scale * t.y := by
  dsimp [synthesize]
  calc
    _ = ((cramer a₁ a₂ t.x t.y).left * a₁.y +
        (cramer a₁ a₂ t.x t.y).right * a₂.y) *
        (cramer b₁ b₂ (-t.x) (-t.y)).scale := by ring
    _ = _ := by rw [cramer_y]; ring

theorem synthesize_bx (a₁ a₂ b₁ b₂ : Row) (t : Target) :
    (synthesize a₁ a₂ b₁ b₂ t).b₁ * b₁.x +
      (synthesize a₁ a₂ b₁ b₂ t).b₂ * b₂.x =
      -((synthesize a₁ a₂ b₁ b₂ t).scale * t.x) := by
  dsimp [synthesize]
  calc
    _ = ((cramer b₁ b₂ (-t.x) (-t.y)).left * b₁.x +
        (cramer b₁ b₂ (-t.x) (-t.y)).right * b₂.x) *
        (cramer a₁ a₂ t.x t.y).scale := by ring
    _ = _ := by rw [cramer_x]; ring

theorem synthesize_by (a₁ a₂ b₁ b₂ : Row) (t : Target) :
    (synthesize a₁ a₂ b₁ b₂ t).b₁ * b₁.y +
      (synthesize a₁ a₂ b₁ b₂ t).b₂ * b₂.y =
      -((synthesize a₁ a₂ b₁ b₂ t).scale * t.y) := by
  dsimp [synthesize]
  calc
    _ = ((cramer b₁ b₂ (-t.x) (-t.y)).left * b₁.y +
        (cramer b₁ b₂ (-t.x) (-t.y)).right * b₂.y) *
        (cramer a₁ a₂ t.x t.y).scale := by ring
    _ = _ := by rw [cramer_y]; ring

def FastCheck (a₁ a₂ b₁ b₂ : Row) (t : Target) : Prop :=
  let w := synthesize a₁ a₂ b₁ b₂ t
  0 ≤ w.a₁ ∧ 0 ≤ w.a₂ ∧ 0 ≤ w.b₁ ∧ 0 ≤ w.b₂ ∧ 0 < w.scale ∧
  w.constant a₁ a₂ b₁ b₂ ≤ w.scale * t.constant ∧
  (w.constant a₁ a₂ b₁ b₂ < w.scale * t.constant ∨
    (0 < w.a₁ ∧ a₁.strict = true) ∨ (0 < w.a₂ ∧ a₂.strict = true) ∨
    (0 < w.b₁ ∧ b₁.strict = true) ∨ (0 < w.b₂ ∧ b₂.strict = true))

instance (a₁ a₂ b₁ b₂ : Row) (t : Target) :
    Decidable (FastCheck a₁ a₂ b₁ b₂ t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem FastCheck.toCheck {a₁ a₂ b₁ b₂ : Row} {t : Target}
    (h : FastCheck a₁ a₂ b₁ b₂ t) : Check a₁ a₂ b₁ b₂ t := by
  obtain ⟨h₁, h₂, h₃, h₄, hs, hc, hstrict⟩ := h
  exact ⟨h₁, h₂, h₃, h₄, hs, synthesize_ax _ _ _ _ _,
    synthesize_ay _ _ _ _ _, synthesize_bx _ _ _ _ _,
    synthesize_by _ _ _ _ _, hc, hstrict⟩

#print axioms FastCheck.toCheck

end N12Compact.PairSupport
