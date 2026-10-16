import Compact.Bridge.IndexedBlockedTarget
import Compact.Core.RowMaterializeSyntax
import Lean.Elab.Command

/-! Explicit whole-target recipes, with separately checked opaque records.
The batch command shares declaration scaffolding, not numerical assumptions.
Each record still receives its own complete ordinary kernel check.
-/

namespace N12Compact.IndexedBlockedTargetSyntax
open Lean Elab Command

abbrev PlanFor {r m a : Nat} (_ : IndexedRelaxation.Dictionary r m a) :=
  IndexedBlockedTarget.Plan r m

def poseRows {r m a : Nat} (d : IndexedRelaxation.Dictionary r m a) (source : Fin m) :=
  (d.poseRows source).map d.rows

def blockRows {r m a : Nat} (d : IndexedRelaxation.Dictionary r m a)
    (block : Option (List (Fin r))) := (block.getD []).map d.rows

syntax "cached_blocked_target%(" term "," term "," term "," term ")"
  "[" term,* "]" : term

macro_rules
  | `(cached_blocked_target%($dictionary:term, $source:term, $block:term, $target:term)
      [$hints:term,*]) =>
      `(⟨$source, $block, some $target,
          materialize_rows% (N12Compact.IndexedBlockedTargetSyntax.poseRows $dictionary $source),
          materialize_rows% (N12Compact.IndexedBlockedTargetSyntax.blockRows $dictionary $block),
          materialize_rows% (N12Compact.IndexedBlockedTargetSyntax.poseRows $dictionary $target),
          [$hints,*]⟩)

declare_syntax_cat blockedTargetRecord
syntax ident "(" term "," term "," term ")" "[" term,* "]" : blockedTargetRecord
syntax ident " empty(" term ")" : blockedTargetRecord

syntax "checked_blocked_batch " ident "(" term ")"
  "[" blockedTargetRecord,* "]" : command

elab_rules : command
  | `(checked_blocked_batch $namespaceName:ident ($dictionary:term)
      [$records:blockedTargetRecord,*]) => do
      elabCommand (← `(namespace $namespaceName))
      let mut names : Array (TSyntax `term) := #[]
      let mut checks : Array (TSyntax `term) := #[]
      for record in records.getElems do
        let (name, value) ← match record with
          | `(blockedTargetRecord| $name:ident ($source:term, $block:term, $target:term)
              [$hints:term,*]) => do
              let value ← `(cached_blocked_target%($dictionary, $source, $block, $target)[$hints,*])
              pure (name, value)
          | `(blockedTargetRecord| $name:ident empty($source:term)) => do
              let value ← `(⟨$source, some [], none, [], [], [], []⟩)
              pure (name, value)
          | _ => throwUnsupportedSyntax
        let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
        elabCommand (← `(noncomputable def $name :
          N12Compact.IndexedBlockedTargetSyntax.PlanFor $dictionary := $value))
        elabCommand (← `(theorem $checked :
          N12Compact.IndexedBlockedTarget.Plan.Check $name $dictionary := by decide +kernel))
        names := names.push (← `($name:ident))
        checks := checks.push (← `($checked:ident))
      let plansName := mkIdent `plans
      let allName := mkIdent `plans_checked
      elabCommand (← `(noncomputable def $plansName :
        List (N12Compact.IndexedBlockedTargetSyntax.PlanFor $dictionary) := [$names,*]))
      let mut proof ← `(by simp)
      for checked in checks.reverse do
        proof ← `(And.intro $checked $proof)
      elabCommand (← `(theorem $allName :
        ∀ plan ∈ $plansName, N12Compact.IndexedBlockedTarget.Plan.Check plan $dictionary := by
          simp only [$plansName:ident, List.forall_mem_cons]
          exact $proof))
      elabCommand (← `(end $namespaceName))

end N12Compact.IndexedBlockedTargetSyntax
