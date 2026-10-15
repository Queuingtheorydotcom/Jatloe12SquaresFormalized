import Compact.Core.FormSyntax

/-! Materialize a closed derived list of integer rows. As for FormSyntax,
the result is ordinary constructor data, and the caller separately proves
exact equality by an ordinary kernel check. No proof evaluator or oracle. -/

namespace N12Compact.RowMaterializeSyntax
open Lean Elab Term Meta

syntax (name := materializeRows) "materialize_rows% " term : term

elab_rules : term
  | `(materialize_rows% $input:term) => do
      let value ← instantiateMVars (← elabTerm input none)
      if value.hasMVar || value.hasFVar then
        throwErrorAt input "materialize_rows% requires a closed concrete row expression"
      let expected := mkApp (Lean.mkConst ``List [0])
        (Lean.mkConst ``IntegerSupport.Row)
      unless ← isDefEq (← inferType value) expected do
        throwErrorAt input "materialize_rows% expects List Row"
      withTransparency .all do
        reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)

end N12Compact.RowMaterializeSyntax
