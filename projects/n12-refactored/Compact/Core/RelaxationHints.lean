import Compact.Core.RowSupport

/-! Local relaxation witnesses checked on cached integer rows.

Only the chosen source positions are replayed. A data materializer may search
for these positions, but neither its search nor its success is a proof. This
checker preserves strictness and rejects out-of-bounds positions explicitly.
-/

namespace N12Compact.RelaxationHints
open IntegerSupport SparseInteger

def rowAt (rows : List Row) (index : Nat) : Row := rows[index]?.getD zero

private theorem rowAt_mem (rows : List Row) (index : Nat) (bound : index < rows.length) :
    rowAt rows index ∈ rows := by
  simpa only [rowAt, List.getElem?_eq_getElem bound, Option.getD_some]
    using (List.getElem_mem bound)

def singleRows (source : Row) : Fin 2 → Row := ![source, RowSupport.one]

/-- The nonzero source coordinate fixes the positive scale. Constant slack
is weighted against the universally true strict row `1 > 0`. -/
def singleCertificate (source target : Row) : Certificate 2 :=
  let pivot := if source.x = 0 then source.y else source.x
  let component := if source.x = 0 then target.y else target.x
  let scale : Int := pivot.natAbs
  let weight := if pivot < 0 then -component else component
  let slack := scale * target.constant - weight * source.constant
  ⟨[(weight, 0), (slack, 1)], scale⟩

def SingleCheck (source target : Row) : Prop :=
  (singleCertificate source target).Check (singleRows source) target

instance (source target : Row) : Decidable (SingleCheck source target) :=
  inferInstanceAs (Decidable (Certificate.Check _ _ _))

theorem single_sound {source target : Row} (checked : SingleCheck source target)
    (p : Fin 2 → ℝ) (holds : source.Holds p) : target.Holds p := by
  have all : ∀ i : Fin 2, (singleRows source i).Holds p := by
    intro i
    fin_cases i
    · exact holds
    · exact RowSupport.one_holds p
  exact checked.sound p (fun term _ => all term.2)

def constantCertificate (target : Row) : Certificate 1 := ⟨[(target.constant, 0)], 1⟩

def ConstantCheck (target : Row) : Prop :=
  (constantCertificate target).Check (fun _ => RowSupport.one) target

instance (target : Row) : Decidable (ConstantCheck target) :=
  inferInstanceAs (Decidable (Certificate.Check _ _ _))

theorem constant_sound {target : Row} (checked : ConstantCheck target)
    (p : Fin 2 → ℝ) : target.Holds p :=
  checked.sound p (fun _ _ => RowSupport.one_holds p)

inductive Hint where
  | constant
  | copy (source : Nat)
  | single (source : Nat)
  | pair (left right : Nat)
  deriving DecidableEq

def Hint.Check (hint : Hint) (sources : List Row) (target : Row) : Prop :=
  match hint with
  | .constant => ConstantCheck target
  | .copy i => i < sources.length ∧ rowAt sources i = target
  | .single i => i < sources.length ∧ SingleCheck (rowAt sources i) target
  | .pair i j => i < sources.length ∧ j < sources.length ∧
      RowSupport.Check (rowAt sources i) (rowAt sources j) target

instance (hint : Hint) (sources : List Row) (target : Row) :
    Decidable (hint.Check sources target) := by
  cases hint <;> unfold Hint.Check <;> infer_instance

theorem Hint.sound {hint : Hint} {sources : List Row} {target : Row}
    (checked : hint.Check sources target) (p : Fin 2 → ℝ)
    (holds : ∀ source ∈ sources, source.Holds p) : target.Holds p := by
  cases hint with
  | constant => exact constant_sound checked p
  | copy i =>
      rw [← checked.2]
      exact holds _ (rowAt_mem sources i checked.1)
  | single i =>
      exact single_sound checked.2 p (holds _ (rowAt_mem sources i checked.1))
  | pair i j =>
      exact RowSupport.sound checked.2.2 p
        (holds _ (rowAt_mem sources i checked.1))
        (holds _ (rowAt_mem sources j checked.2.1))

/-- Every target receives exactly one checked witness, in target row order.
Missing targets or trailing witnesses are rejected, including empty lists. -/
def Check (sources : List Row) : List Row → List Hint → Prop
  | [], [] => True
  | target :: targets, hint :: hints => hint.Check sources target ∧ Check sources targets hints
  | _, _ => False

instance (sources targets : List Row) (hints : List Hint) :
    Decidable (Check sources targets hints) := by
  induction targets generalizing hints with
  | nil => cases hints <;> unfold Check <;> infer_instance
  | cons target targets ih =>
      cases hints with
      | nil => unfold Check; infer_instance
      | cons hint hints =>
          letI := ih hints
          unfold Check
          infer_instance

theorem sound {sources targets : List Row} {hints : List Hint}
    (checked : Check sources targets hints) (p : Fin 2 → ℝ)
    (holds : ∀ source ∈ sources, source.Holds p) :
    ∀ target ∈ targets, target.Holds p := by
  induction targets generalizing hints with
  | nil => intro target member; cases member
  | cons target targets ih =>
      cases hints with
      | nil => exact False.elim checked
      | cons hint hints =>
          intro other member
          rcases List.mem_cons.mp member with same | later
          · subst other
            exact hint.sound checked.1 p holds
          · exact ih checked.2 other later

#print axioms Hint.sound
#print axioms sound
end N12Compact.RelaxationHints
