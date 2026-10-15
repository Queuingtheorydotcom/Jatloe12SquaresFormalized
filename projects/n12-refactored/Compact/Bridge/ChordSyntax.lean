import Compact.Bridge.IndexedChord
import Compact.Core.RowMaterializeSyntax
import Lean.Elab.Command

/-! Compact chord records elaborate to separate cached data and ordinary
kernel-checked proofs. The commands remove repeated declarations, not proof
obligations: every neighbor bound, target row and empty witness is replayed.
No native evaluator, unchecked cast, or external certificate oracle is used. -/

namespace N12Compact.ChordSyntax
open Lean Elab Command

abbrev BranchFor {r m a : Nat} (_ : IndexedRelaxation.Dictionary r m a) :=
  DirectPruningPlan.Branch m

theorem checked_nil {α : Type} (P : α → Prop) : ∀ entry ∈ ([] : List α), P entry := by
  intro entry member
  exact (List.not_mem_nil member).elim

theorem checked_cons {α : Type} (P : α → Prop) {entry : α} {entries : List α}
    (first : P entry) (rest : ∀ next ∈ entries, P next) :
    ∀ next ∈ entry :: entries, P next := by
  intro next member
  rcases List.mem_cons.mp member with rfl | member
  · exact first
  · exact rest next member

syntax (name := checkedChordCollection) "checked_chord_collection " ident
  " : " term " => " term " := " "[" ident,* "]" : command

elab_rules : command
  | `(checked_chord_collection $name:ident : $type:term => $predicate:term := [$entries:ident,*]) => do
      let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
      let terms : Array (TSyntax `term) := entries.getElems.map fun entry => ⟨entry.raw⟩
      elabCommand (← `(noncomputable def $name : List $type := [$terms,*]))
      let mut proof ← `(checked_nil $predicate)
      for entry in entries.getElems.reverse do
        let entryChecked := mkIdentFrom entry (entry.getId.appendAfter "_checked")
        proof ← `(checked_cons $predicate $entryChecked $proof)
      elabCommand (← `(theorem $checked : ∀ entry ∈ $name, ($predicate) entry := $proof))

syntax "chord_keep%(" term "," term ")" : term
syntax "chord_close%(" term ")" : term

private def emitBranch (name : TSyntax `ident) (dictionary source cut outcome : TSyntax `term) :
    CommandElabM Unit := do
  let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
  let inputs ← `(materialize_rows%
    ($cut :: (($dictionary).poseRows $source).map ($dictionary).rows))
  match outcome with
  | `(chord_keep%($target:term,$hints:term)) =>
      let targets := mkIdentFrom name (name.getId.appendAfter "_targets")
      elabCommand (← `(noncomputable def $name : BranchFor $dictionary :=
        ⟨$inputs, .keep $target $hints⟩))
      elabCommand (← `(noncomputable def $targets : List IntegerSupport.Row :=
        materialize_rows% ((($dictionary).poseRows $target).map ($dictionary).rows)))
      elabCommand (← `(theorem $checked :
        DirectPruningPlan.Branch.Check $name $dictionary $source :=
        IndexedChord.keep_checked $dictionary $source $target ($name).inputs $targets $hints
          rfl (by decide +kernel) (by decide +kernel)))
  | `(chord_close%($witness:term)) =>
      elabCommand (← `(noncomputable def $name : BranchFor $dictionary :=
        ⟨$inputs, .close $witness⟩))
      elabCommand (← `(theorem $checked :
        DirectPruningPlan.Branch.Check $name $dictionary $source := by decide +kernel))
  | _ => throwErrorAt outcome "expected chord_keep%(target,hints) or chord_close%(witness)"

syntax (name := checkedChordNeighbor) "checked_chord_neighbor " ident
  "(" term "," term "," term "," term ")" " := "
  "(" term "," term "," term "," term ")" : command

elab_rules : command
  | `(checked_chord_neighbor $name:ident
      ($dictionary:term,$horizontal:term,$lo:term,$hi:term) :=
      ($source:term,$radius:term,$radiusChecked:term,$hints:term)) => do
      let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
      elabCommand (← `(noncomputable def $name : IndexedChord.Neighbor $dictionary :=
        { source := $source, radius := $radius
          inputs := materialize_rows% ((($dictionary).poseRows $source).map ($dictionary).rows)
          inputs_exact := rfl
          hints := $hints }))
      elabCommand (← `(theorem $checked :
        IndexedChord.Neighbor.Check $name $horizontal $lo $hi :=
        ⟨$radiusChecked, by decide +kernel⟩))

syntax (name := checkedChordPlan) "checked_chord_plan " ident
  "(" term "," term "," term "," term ")" " := "
  "(" term "," term "," term "," term "," term ")" : command

elab_rules : command
  | `(checked_chord_plan $name:ident
      ($dictionary:term,$horizontal:term,$lo:term,$hi:term) :=
      ($source:term,$radius:term,$radiusChecked:term,$low:term,$high:term)) => do
      let lowName := mkIdentFrom name (name.getId.appendAfter "_low")
      let highName := mkIdentFrom name (name.getId.appendAfter "_high")
      let lowChecked := mkIdentFrom lowName (lowName.getId.appendAfter "_checked")
      let highChecked := mkIdentFrom highName (highName.getId.appendAfter "_checked")
      let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
      emitBranch lowName dictionary source
        (← `(AxisSection.upper $horizontal ($lo - ($radius).radius) true)) low
      emitBranch highName dictionary source
        (← `(AxisSection.lower $horizontal ($hi + ($radius).radius) true)) high
      elabCommand (← `(noncomputable def $name : IndexedChord.Plan $dictionary $horizontal $lo $hi :=
        ⟨$source,$radius,$lowName,$highName,rfl,rfl⟩))
      elabCommand (← `(theorem $checked : IndexedChord.Plan.Check $name :=
        ⟨$radiusChecked,$lowChecked,$highChecked⟩))

end N12Compact.ChordSyntax
