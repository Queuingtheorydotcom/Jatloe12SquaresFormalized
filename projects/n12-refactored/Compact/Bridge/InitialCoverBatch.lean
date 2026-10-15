import Compact.Bridge.CheckedRecipeCommand

/-! A bounded initial-cover batch shares declaration and list-proof scaffolding.
Each record still invokes `checked_recipe` separately, producing its own cache
and opaque kernel-checked numerical theorem. The batch proof only composes
those theorems by list induction; it performs no combined numerical decision.
Fully qualified batch names preserve the original public entry namespace.
-/

namespace N12Compact.InitialCoverBatch

theorem checked_nil {α : Type} (P : α → Prop) : ∀ x ∈ ([] : List α), P x := by
  intro x member
  cases member

theorem checked_cons {α : Type} {P : α → Prop} {x : α} {xs : List α}
    (head : P x) (tail : ∀ y ∈ xs, P y) : ∀ y ∈ x :: xs, P y := by
  intro y member
  rcases List.mem_cons.mp member with equal | member
  · subst y
    exact head
  · exact tail y member

end N12Compact.InitialCoverBatch

namespace N12Compact.InitialCoverBatchSyntax
open Lean Elab Command

declare_syntax_cat initialCoverRecord
syntax ident " := " term : initialCoverRecord
syntax (name := checkedInitialBatch) "checked_initial_batch " ident
  "(" term "," term "," term ")"
  "[" initialCoverRecord,* "]" : command

elab_rules : command
  | `(checked_initial_batch $batch:ident ($bank:term, $inside:term, $outside:term)
      [$records:initialCoverRecord,*]) => do
      let records := records.getElems
      unless decide (0 < records.size ∧ records.size ≤ 8) do
        throwErrorAt batch "an initial-cover batch must contain one to eight records"
      let namespacePrefix := batch.getId.getPrefix
      -- These are the same options as the historical bounded batch modules.
      withOptions (fun options =>
          let options := options.setBool `Elab.async false
          let options := options.setNat `maxRecDepth 100000
          let options := options.setNat `maxHeartbeats 0
          options.setBool `linter.unnecessarySeqFocus false) do
        let mut names : Array (TSyntax `ident) := #[]
        let mut used : Array Name := #[]
        for record in records do
          match record with
          | `(initialCoverRecord| $name:ident := $spec:term) =>
              unless name.getId.isAtomic && !used.contains name.getId do
                throwErrorAt name "entry names must be distinct unqualified identifiers"
              used := used.push name.getId
              let full := mkIdentFrom name (namespacePrefix ++ name.getId)
              names := names.push full
              elabCommand (← `(checked_recipe $full ($bank, $inside, $outside) := $spec))
          | _ => throwErrorAt record "expected a named initial-cover recipe"
        let entries : Array (TSyntax `term) := names.map fun name => ⟨name.raw⟩
        let literal := mkIdentFrom batch (batch.getId.appendAfter "_literal_checked")
        let checked := mkIdentFrom batch (batch.getId.appendAfter "_checked")
        elabCommand (← `(noncomputable def $batch :
          List (N12Compact.DirectRecipeTable.Entry $bank $inside $outside) := [$entries,*]))
        let mut proof ← `(N12Compact.InitialCoverBatch.checked_nil
          N12Compact.DirectRecipeCheck.LiteralCheck)
        for name in names.reverse do
          let fact := mkIdentFrom name (name.getId.appendAfter "_literal_checked")
          proof ← `(N12Compact.InitialCoverBatch.checked_cons $fact $proof)
        elabCommand (← `(theorem $literal :
            ∀ entry ∈ $batch, N12Compact.DirectRecipeCheck.LiteralCheck entry := $proof))
        elabCommand (← `(theorem $checked : ∀ entry ∈ $batch, entry.Check :=
          N12Compact.DirectRecipeCheck.all_checked $batch $literal))

end N12Compact.InitialCoverBatchSyntax
