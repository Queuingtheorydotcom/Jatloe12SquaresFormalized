import S12.LinearCertificate

namespace S12

def LinearConstraint.opposite {n : Nat} (r : LinearConstraint n) : LinearConstraint n :=
  ⟨r.form.scale (-1),!r.strict⟩

theorem LinearConstraint.opposite_holds {n : Nat} (r : LinearConstraint n) (x : Fin n→ℝ) :
    r.opposite.Holds x ↔ ¬r.Holds x := by
  cases r with
  | mk form strict =>
    cases strict <;> simp [LinearConstraint.opposite,LinearConstraint.Holds]

/-- A rational Farkas certificate for an implication. The target's exact
strictness is included by adding its logical negation to the input system. -/
def LinearImplicationCheck {n : Nat} (inputs : List (LinearConstraint n))
    (target : LinearConstraint n) (terms : List (ℚ × LinearConstraint n)) : Prop :=
  LinearCertificateCheck (target.opposite::inputs) terms
instance decidableLinearImplicationCheck {n : Nat} (inputs : List (LinearConstraint n))
    (target : LinearConstraint n) (terms : List (ℚ × LinearConstraint n)) :
    Decidable (LinearImplicationCheck inputs target terms) := inferInstanceAs (Decidable (LinearCertificateCheck _ _))

theorem linear_implication_sound {n : Nat} (inputs : List (LinearConstraint n))
    (target : LinearConstraint n) (terms : List (ℚ × LinearConstraint n))
    (hc : LinearImplicationCheck inputs target terms) (x : Fin n→ℝ)
    (hx : ∀ r∈inputs,r.Holds x) : target.Holds x := by
  by_contra he
  apply linear_certificate_sound _ terms hc
  refine ⟨x,?_⟩
  intro r hr
  rcases List.mem_cons.mp hr with hr | hr
  · subst r; exact (LinearConstraint.opposite_holds target x).mpr he
  · exact hx r hr

#print axioms linear_implication_sound
end S12
