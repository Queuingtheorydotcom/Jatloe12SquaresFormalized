import Compact.Bridge.DirectRecipeCheck
import Lean.Elab.Command

/-! One semantic recipe record produces two separate ordinary declarations:
its cached entry and its checked integer certificate. The command only removes
repeated source scaffolding. It invokes normal elaboration for both declarations;
the numerical theorem is still proved by `decide +kernel`, and each record has
its own named proof rather than one accumulated decision for the whole table.

The public theorem for an entry named `entry` is `entry_literal_checked`.
Neither the recipe materializers nor this syntax extend the proof trust boundary.
-/

namespace N12Compact.CheckedRecipeCommand
open Lean Elab Command

syntax (name := checkedRecipe) "checked_recipe " ident
  "(" term "," term "," term ")" " := " term : command

elab_rules : command
  | `(checked_recipe $name:ident ($bank:term, $inside:term, $outside:term) := $spec:term) => do
      let checked := mkIdentFrom name (name.getId.appendAfter "_literal_checked")
      elabCommand (← `(noncomputable def $name :
        N12Compact.DirectRecipeTable.Entry $bank $inside $outside :=
          (cached_recipe_table%($bank, $inside, $outside)[$spec]).head
            (by intro impossible; cases impossible)))
      elabCommand (← `(theorem $checked :
        N12Compact.DirectRecipeCheck.LiteralCheck $name := by decide +kernel))

end N12Compact.CheckedRecipeCommand
