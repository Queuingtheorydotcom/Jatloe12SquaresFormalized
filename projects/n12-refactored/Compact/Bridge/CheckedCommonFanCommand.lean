import Compact.Bridge.IndexedCommonContext
import Compact.Core.BoundaryFanSyntax
import Lean.Elab.Command

/-! One original pose/block/cycle record supplies a separately checked fan,
its exact numeric cache and its original-pose semantic context. The optional
additional bindings of the same cache still use `bind_common_context` and
prove their own input/reference identities. Every numeric Check remains an
ordinary named theorem; there is no table-wide numerical proof accumulator. -/

namespace N12Compact.CheckedCommonFanCommand
open Lean Elab Command

syntax (name := checkedCommonFan) "checked_common_fan " ident
  "(" term "," term ")" " := " term " using " term : command

elab_rules : command
  | `(checked_common_fan $name:ident ($dictionary:term, $directions:term)
      := $input:term using $cycle:term) => do
      let header := mkIdentFrom name (name.getId.appendAfter "_header")
      let raw := mkIdentFrom name (name.getId.appendAfter "_raw")
      let checked := mkIdentFrom name (name.getId.appendAfter "_raw_checked")
      let numeric := mkIdentFrom name (name.getId.appendAfter "_numeric")
      let cache := mkIdentFrom name (name.getId.appendAfter "_cache")
      let reference := mkIdentFrom name (name.getId.appendAfter "_reference")
      elabCommand (← `(noncomputable def $header :
        N12Compact.IndexedCommonGroups.Header $dictionary := $input))
      elabCommand (← `(noncomputable def $raw := materialize_boundary_fan%
        (N12Compact.BoundaryFan.context ($dictionary).rows
          (($header).block ++ ($dictionary).poseRows ($header).pose)
          (N12Compact.HistoricalPoseFanRecipe.reference
            (($dictionary).angles (($dictionary).poseAngle ($header).pose)).val)
          $directions $cycle)))
      elabCommand (← `(theorem $checked : ($raw).Check ($dictionary).rows := by
        decide +kernel))
      elabCommand (← `(noncomputable def $numeric : N12Compact.RawSupportFan.Context :=
        materialize_raw_fan% (($raw).certify ($dictionary).rows $checked).numeric))
      elabCommand (← `(noncomputable def $cache :
        N12Compact.IndexedCommonGroups.FanCache $dictionary :=
        ⟨$raw, $checked, $numeric, by rfl⟩))
      elabCommand (← `(theorem $reference : ($cache).raw.reference =
          N12Compact.HistoricalPoseFanRecipe.reference
            (($dictionary).angles (($dictionary).poseAngle ($header).pose)).val := by
        decide +kernel))
      elabCommand (← `(noncomputable def $name :
        N12Compact.IndexedCommonGroups.Context $dictionary :=
        ($cache).bind $header (by rfl) $reference))

end N12Compact.CheckedCommonFanCommand
