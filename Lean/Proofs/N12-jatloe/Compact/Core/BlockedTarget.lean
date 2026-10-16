import Compact.Core.RelaxationHints
import Compact.Core.EmptyContext
import Compact.Core.RegionDAG

/-! Whole-target pruning by a checked contrapositive.

For each final inequality, either the incoming rows already imply it, or its
exact strict complement forces the entire excluded conjunction. This replaces
repeated proofs of all final inequalities in every outside-face context.
-/

set_option Elab.async false

namespace N12Compact.BlockedTarget
open IntegerSupport

inductive Hint (inputCount : Nat) where
  | direct (hint : RelaxationHints.Hint)
  | block (hints : List RelaxationHints.Hint)
  | impossible (witness : EmptyContext.Witness (inputCount + 1))

def violationRows (inputs : List Row) (target : Row) : Fin (inputs.length + 1) → Row :=
  fun i => RelaxationHints.rowAt (RegionDAG.opposite target :: inputs) i.val

def Hint.Check {inputs : List Row} (hint : Hint inputs.length)
    (block : List Row) (target : Row) : Prop :=
  match hint with
  | .direct h => h.Check inputs target
  | .block hs => RelaxationHints.Check (RegionDAG.opposite target :: inputs) block hs
  | .impossible w => w.Check (violationRows inputs target)

instance {inputs : List Row} (hint : Hint inputs.length) (block : List Row) (target : Row) :
    Decidable (hint.Check (inputs := inputs) block target) := by
  cases hint <;> unfold Hint.Check <;> infer_instance

private theorem violation_holds (inputs : List Row) (target : Row) (p : Fin 2 → ℝ)
    (incoming : ∀ row ∈ inputs, row.Holds p) (fails : ¬ target.Holds p) :
    ∀ i, (violationRows inputs target i).Holds p := by
  intro i
  have bound : i.val < (RegionDAG.opposite target :: inputs).length := by
    simpa only [List.length_cons] using i.isLt
  have all : ∀ row ∈ RegionDAG.opposite target :: inputs, row.Holds p := by
    intro row member
    rcases List.mem_cons.mp member with rfl | member
    · exact (RegionDAG.opposite_holds target p).mpr fails
    · exact incoming row member
  simpa only [violationRows, RelaxationHints.rowAt,
    List.getElem?_eq_getElem bound, Option.getD_some] using
    all _ (List.getElem_mem bound)

theorem Hint.sound {inputs : List Row} {hint : Hint inputs.length}
    {block : List Row} {target : Row} (checked : hint.Check (inputs := inputs) block target)
    (p : Fin 2 → ℝ) (incoming : ∀ row ∈ inputs, row.Holds p)
    (excluded : ¬ (∀ row ∈ block, row.Holds p)) : target.Holds p := by
  classical
  cases hint with
  | direct h => exact h.sound checked p incoming
  | block hs =>
      by_contra fails
      apply excluded
      apply RelaxationHints.sound checked p
      intro row member
      rcases List.mem_cons.mp member with rfl | member
      · exact (RegionDAG.opposite_holds target p).mpr fails
      · exact incoming row member
  | impossible w =>
      by_contra fails
      exact w.sound (violationRows inputs target) checked p
        (fun i _ => violation_holds inputs target p incoming fails i)

def Hint.Independent {n : Nat} : Hint n → Prop
  | .direct _ => True
  | .block _ => False
  | .impossible _ => True

instance {n : Nat} (hint : Hint n) : Decidable hint.Independent := by
  cases hint <;> unfold Hint.Independent <;> infer_instance

theorem Hint.source_sound {inputs : List Row} {hint : Hint inputs.length}
    {block : List Row} {target : Row} (checked : hint.Check (inputs := inputs) block target)
    (independent : hint.Independent) (p : Fin 2 → ℝ)
    (incoming : ∀ row ∈ inputs, row.Holds p) : target.Holds p := by
  classical
  cases hint with
  | direct h => exact h.sound checked p incoming
  | block hs => exact False.elim independent
  | impossible w =>
      by_contra fails
      exact w.sound (violationRows inputs target) checked p
        (fun i _ => violation_holds inputs target p incoming fails i)

def Check (inputs block : List Row) : List Row → List (Hint inputs.length) → Prop
  | [], [] => True
  | target :: targets, hint :: hints =>
      hint.Check (inputs := inputs) block target ∧ Check inputs block targets hints
  | _, _ => False

instance (inputs block targets : List Row) (hints : List (Hint inputs.length)) :
    Decidable (Check inputs block targets hints) := by
  induction targets generalizing hints with
  | nil => cases hints <;> unfold Check <;> infer_instance
  | cons target targets ih =>
      cases hints with
      | nil => unfold Check; infer_instance
      | cons hint hints =>
          letI := ih hints
          unfold Check
          infer_instance

theorem sound {inputs block targets : List Row} {hints : List (Hint inputs.length)}
    (checked : Check inputs block targets hints) (p : Fin 2 → ℝ)
    (incoming : ∀ row ∈ inputs, row.Holds p)
    (excluded : ¬ (∀ row ∈ block, row.Holds p)) :
    ∀ target ∈ targets, target.Holds p := by
  induction targets generalizing hints with
  | nil => intro target member; cases member
  | cons target targets ih =>
      cases hints with
      | nil => exact False.elim checked
      | cons hint hints =>
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · exact Hint.sound checked.1 p incoming excluded
          · exact ih checked.2 other member

theorem source_sound {inputs block targets : List Row} {hints : List (Hint inputs.length)}
    (checked : Check inputs block targets hints)
    (independent : ∀ hint ∈ hints, hint.Independent) (p : Fin 2 → ℝ)
    (incoming : ∀ row ∈ inputs, row.Holds p) :
    ∀ target ∈ targets, target.Holds p := by
  induction targets generalizing hints with
  | nil => intro target member; cases member
  | cons target targets ih =>
      cases hints with
      | nil => exact False.elim checked
      | cons hint hints =>
          intro other member
          rcases List.mem_cons.mp member with rfl | member
          · exact Hint.source_sound checked.1
              (independent hint (List.mem_cons_self)) p incoming
          · exact ih checked.2
              (fun h hh => independent h (List.mem_cons_of_mem _ hh)) other member

#print axioms sound
end N12Compact.BlockedTarget
