import Compact.Bridge.DirectPoseForms
import Lean.Elab.Term
import Lean.Meta.Reduce

/-! One-time materialization of exact derived integer forms.

The elaborator reduces a closed transparent form expression into ordinary
constructor data. It uses Lean's definitional reducer, not compiled code or an
external evaluator. Clients prove the resulting data equal to their original
geometric expression by `rfl`; that equality is independently kernel checked.
No proof is manufactured by this elaborator.
-/

namespace N12Compact.FormSyntax
open Lean Elab Term Meta

syntax (name := materializeForms) "materialize_forms% " term : term

elab_rules : term
  | `(materialize_forms% $input:term) => do
      let value ← instantiateMVars (← elabTerm input none)
      if value.hasMVar || value.hasFVar then
        throwErrorAt input "materialize_forms% requires a closed concrete form expression"
      let type ← inferType value
      let forms := mkApp (Lean.mkConst ``List [0])
        (Lean.mkConst ``DirectPoseCover.Form)
      let blocks := mkApp (Lean.mkConst ``List [0]) forms
      unless (← isDefEq type forms) || (← isDefEq type blocks) do
        throwErrorAt input "materialize_forms% expects List Form or List (List Form)"
      withTransparency .all do
        reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)

end N12Compact.FormSyntax
