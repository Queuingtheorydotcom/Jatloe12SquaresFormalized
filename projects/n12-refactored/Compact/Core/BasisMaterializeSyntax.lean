import Compact.Core.VertexFromRows
import Lean.Elab.Term
import Lean.Meta.Reduce

/-!
Materialize a closed derived basis once, so subsequent pair checks operate on
literal integer data instead of traversing the shared row dictionary again.
This elaborator emits data only. `Entry.Check` independently checks the actual
row identities and vertex equations in the kernel before any geometric use.
-/

namespace N12Compact.BasisMaterializeSyntax
open Lean Elab Term Meta

syntax (name := materializeBasis) "materialize_basis% " term : term

elab_rules : term
  | `(materialize_basis% $input:term) => do
      let value ← instantiateMVars (← elabTerm input none)
      if value.hasMVar || value.hasFVar then
        throwErrorAt input "materialize_basis% requires a closed concrete basis expression"
      unless ← isDefEq (← inferType value) (Lean.mkConst ``VertexSupport.Basis) do
        throwErrorAt input "materialize_basis% expects VertexSupport.Basis"
      withTransparency .all do
        reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)

end N12Compact.BasisMaterializeSyntax
