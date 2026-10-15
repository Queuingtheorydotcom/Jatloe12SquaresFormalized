import Compact.Bridge.IndexedCommonContext
import Lean.Elab.Command

/-! Commands remove repeated wrapper scaffolding only. The raw fan has an
ordinary checker proof, every cache is definitionally exact, and every actual
pose/block use receives separate kernel-checked input/reference identities. -/

namespace N12Compact.CheckedCommonContext
open Lean Elab Command

syntax (name := cacheCommonFan) "cache_common_fan " ident
  "(" term "," term "," term ")" : command
syntax (name := bindCommonContext) "bind_common_context " ident
  "(" term "," term ")" " := " term : command
syntax (name := checkedEmptyContext) "checked_empty_context " ident
  "(" term ")" " := " term " using " term : command

elab_rules : command
  | `(cache_common_fan $name:ident ($dictionary:term, $raw:term, $checked:term)) => do
      let numeric := mkIdentFrom name (name.getId.appendAfter "_numeric")
      elabCommand (← `(noncomputable def $numeric : N12Compact.RawSupportFan.Context :=
        materialize_raw_fan% (($raw).certify ($dictionary).rows $checked).numeric))
      elabCommand (← `(noncomputable def $name :
          N12Compact.IndexedCommonGroups.FanCache $dictionary :=
        ⟨$raw, $checked, $numeric, by rfl⟩))
  | `(bind_common_context $name:ident ($dictionary:term, $cache:term) := $input:term) => do
      let header := mkIdentFrom name (name.getId.appendAfter "_header")
      let inputs := mkIdentFrom name (name.getId.appendAfter "_inputs")
      let reference := mkIdentFrom name (name.getId.appendAfter "_reference")
      elabCommand (← `(noncomputable def $header :
        N12Compact.IndexedCommonGroups.Header $dictionary := $input))
      elabCommand (← `(theorem $inputs : ($cache).raw.inputs =
          ($header).block ++ ($dictionary).poseRows ($header).pose := by decide +kernel))
      elabCommand (← `(theorem $reference : ($cache).raw.reference =
          N12Compact.HistoricalPoseFanRecipe.reference
            (($dictionary).angles (($dictionary).poseAngle ($header).pose)).val := by
        decide +kernel))
      elabCommand (← `(noncomputable def $name :=
        ($cache).bind $header $inputs $reference))
  | `(checked_empty_context $name:ident ($dictionary:term) := $header:term using $terms:term) => do
      let head := mkIdentFrom name (name.getId.appendAfter "_header")
      let witness := mkIdentFrom name (name.getId.appendAfter "_witness")
      let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
      elabCommand (← `(noncomputable def $head :
        N12Compact.IndexedCommonGroups.Header $dictionary := $header))
      elabCommand (← `(noncomputable def $witness :=
        (show N12Compact.EmptyContext.Witness _ from
          ⟨($head).block ++ ($dictionary).poseRows ($head).pose, $terms⟩)))
      elabCommand (← `(theorem $checked : ($witness).Check ($dictionary).rows := by decide +kernel))
      elabCommand (← `(noncomputable def $name :
        N12Compact.IndexedCommonGroups.Context $dictionary :=
          .empty $head $witness rfl $checked))

end N12Compact.CheckedCommonContext
