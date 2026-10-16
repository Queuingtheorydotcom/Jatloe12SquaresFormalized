import S12.LocalQueryData
import S12.CertifiedDomain
import Lean.Elab.Command

/-! Historical entrances reuse the same checked local geometric queries.
Selecting an existing query introduces no new arithmetic check. A genuinely
new query is declared and checked once, then shared as a certified value.
Existing foundational query proofs keep their original trust boundary.
-/

namespace N12Compact.SharedLocalQueries
open S12

def select (queries : List LocalQuery)
    (checked : queries.all (fun query => decide query.Check) = true)
    (index : Fin queries.length) : {query : LocalQuery // query.Check} :=
  ⟨queries.get index,
    of_decide_eq_true (List.all_eq_true.mp checked _ (List.get_mem queries index))⟩

/-- The original domain filter, consuming a shared certified query value. -/
def remove (family : Finset Nat) (domain : CertifiedDomain family)
    (query : {query : LocalQuery // query.Check})
    (same_mask : query.val.mask = domain.mask) (combined : query.val.kind = 2) :
    CertifiedDomain family :=
  CertifiedDomain.remove family domain query.val query.property same_mask combined

end N12Compact.SharedLocalQueries

namespace N12Compact.SharedLocalQuerySyntax
open Lean Elab Command Term

syntax (name := certifiedExistingQuery) "certified_query% " num : term
syntax (name := checkedSharedQuery) "checked_local_query " ident " := " term : command

elab_rules : term
  | `(certified_query% $index:num) => do
      let chunk := mkIdent (Name.str (Name.mkSimple "S12") s!"queryChunk{index.getNat / 50}")
      let checked := mkIdent (Name.str (Name.mkSimple "S12") s!"queryChunk{index.getNat / 50}_checked")
      let offset : TSyntax `term := ⟨Syntax.mkNumLit (toString (index.getNat % 50))⟩
      let expression ← `(N12Compact.SharedLocalQueries.select $chunk $checked ⟨$offset, by decide⟩)
      elabTerm expression none

elab_rules : command
  | `(checked_local_query $name:ident := $value:term) => do
      let checked := mkIdentFrom name (name.getId.appendAfter "_checked")
      let certified := mkIdentFrom name (name.getId.appendAfter "_certified")
      elabCommand (← `(noncomputable def $name : S12.LocalQuery := $value))
      elabCommand (← `(theorem $checked : ($name).Check := by decide +kernel))
      elabCommand (← `(noncomputable def $certified :
        {query : S12.LocalQuery // query.Check} := ⟨$name, $checked⟩))

end N12Compact.SharedLocalQuerySyntax
