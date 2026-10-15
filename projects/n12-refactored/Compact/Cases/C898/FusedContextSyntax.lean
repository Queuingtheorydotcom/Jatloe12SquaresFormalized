import Compact.Cases.C898.CachedPairFan
import Compact.Core.BoundaryFanSyntax
import Compact.Core.BasisMaterializeSyntax
import Lean.Elab.Command

/-! One original pose/block/fan record supplies its checked semantic context
and its exact numeric view. Inputs and reference values are derived once from
the original dictionary. Every fan still passes the ordinary row-membership
and vertex checker; later common-point and pair checks are unchanged. -/

namespace N12Compact.C898Cached.FusedContext
open C898Shared CachedSupportFan VertexFanTable

structure Header where
  pose : Fin poseCount
  block : List (Fin rowCount)
  keyAngle : Fin 64

noncomputable def Header.inputs (header : Header) : List (Fin rowCount) :=
  header.block ++ poseRows header.pose

noncomputable def Header.reference (header : Header) : ReferenceAxis.Reference :=
  references (poseAngle header.pose)

noncomputable def Header.bind (header : Header) (raw : RawContext rowCount)
    (checked : raw.Check rows) (inputs : raw.inputs = header.inputs)
    (reference : raw.reference = header.reference) : PoseContext where
  pose := header.pose
  block := header.block
  keyAngle := header.keyAngle
  context := raw.certify rows checked
  inputs_exact := inputs
  reference_exact := reference

end N12Compact.C898Cached.FusedContext

namespace N12Compact.C898Cached.FusedContextSyntax
open Lean Elab Command

syntax "c898_cycle%(" term "," term ")" : term
syntax "c898_entries%(" term ")" : term
syntax (name := checkedC898Fan) "checked_c898_fan " ident ident
  " := " term " using " term : command

elab_rules : command
  | `(checked_c898_fan $name:ident $numeric:ident := $input:term using $fan:term) => do
      let header := mkIdentFrom name (name.getId.appendAfter "_header")
      let raw := mkIdentFrom name (name.getId.appendAfter "_raw")
      let checked := mkIdentFrom name (name.getId.appendAfter "_raw_checked")
      let reference := mkIdentFrom name (name.getId.appendAfter "_reference")
      let exactProof := mkIdentFrom numeric (numeric.getId.appendAfter "_exact")
      elabCommand (← `(noncomputable def $header :
        N12Compact.C898Cached.FusedContext.Header := $input))
      let rawTerm ← match fan with
        | `(c898_cycle%($directions:term,$cycle:term)) =>
            `(materialize_boundary_fan%
              (N12Compact.BoundaryFan.context N12Compact.C898Shared.rows
                ($header).inputs ($header).reference $directions $cycle))
        | `(c898_entries%($entries:term)) =>
            `(materialize_boundary_fan%
              (show N12Compact.VertexFanTable.RawContext N12Compact.C898Shared.rowCount from
                ⟨($header).inputs, ($header).reference, $entries⟩))
        | _ => throwErrorAt fan "expected c898_cycle%(directions,rows) or c898_entries%(entries)"
      elabCommand (← `(noncomputable def $raw :
        N12Compact.VertexFanTable.RawContext N12Compact.C898Shared.rowCount := $rawTerm))
      elabCommand (← `(theorem $checked :
        ($raw).Check N12Compact.C898Shared.rows := by decide +kernel))
      elabCommand (← `(theorem $reference :
        ($raw).reference = ($header).reference := by decide +kernel))
      elabCommand (← `(noncomputable def $name : N12Compact.C898Cached.PoseContext :=
        ($header).bind $raw $checked (by rfl) $reference))
      elabCommand (← `(noncomputable def $numeric : N12Compact.RawSupportFan.Context :=
        materialize_raw_fan% ($name).context.numeric))
      elabCommand (← `(theorem $exactProof : $numeric = ($name).context.numeric := rfl))

end N12Compact.C898Cached.FusedContextSyntax
