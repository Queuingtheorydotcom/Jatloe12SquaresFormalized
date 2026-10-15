import Compact.Core.PlanarBoundaryHints
import Lean.Elab.Term
import Lean.Meta.Reduce

/-! Untrusted, bounded construction of whole-line exclusion hints.

Only the closed base and forbidden row lists are reduced. The expensive
recursive `PlanarBoundaryAuto.activeRows` expression is never reduced.
The elaborator scans small literal arrays, emitting ordinary constructors.
`boundary_cache%` separately checks the chosen hints and retained-row equality
in the kernel. Search completeness or optimality is not a proof assumption:
an unrecognized exclusion simply leaves that boundary in the numerical test.
No external data, compiled proof evaluator or new axiom is used.
-/

namespace N12Compact.BoundaryHintSyntax
open Lean Elab Term Meta IntegerSupport PlanarBoundaryFilter

private def natural (value : Expr) : TermElabM Nat := do
  let some n := value.rawNatLit?
    | throwError "boundary hints expected a natural-number constructor"
  return n

private def integer (value : Expr) : TermElabM Int := do
  if value.isAppOfArity ``Int.ofNat 1 then
    return Int.ofNat (← natural value.getAppArgs[0]!)
  else if value.isAppOfArity ``Int.negSucc 1 then
    return Int.negSucc (← natural value.getAppArgs[0]!)
  else
    throwError "boundary hints expected an integer constructor"

private def readRow (value : Expr) : TermElabM Row := do
  unless value.isAppOfArity ``Row.mk 4 do
    throwError "boundary hints expected an integer Row constructor"
  let args := value.getAppArgs
  let strict ← if args[3]!.isConstOf ``Bool.true then pure true
    else if args[3]!.isConstOf ``Bool.false then pure false
    else throwError "boundary hints expected a literal strictness flag"
  return ⟨← integer args[0]!, ← integer args[1]!, ← integer args[2]!, strict⟩

private def readList (value : Expr) : TermElabM (Array Expr) := do
  let mut cursor := value
  let mut result := #[]
  while cursor.isAppOfArity ``List.cons 3 do
    let args := cursor.getAppArgs
    result := result.push args[1]!
    if result.size > 128 then
      throwError "boundary hints local list limit exceeded (128)"
    cursor := args[2]!
  unless cursor.isAppOfArity ``List.nil 1 do
    throwError "boundary hints expected a closed literal list"
  return result

private def closedRows (input : Syntax) (nested : Bool) :
    TermElabM (Array Row) := do
  let value ← instantiateMVars (← elabTermAndSynthesize input none)
  if value.hasMVar || value.hasFVar then
    throwErrorAt input "boundary hints require closed concrete rows"
  let rowList := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Row)
  let expected := if nested then mkApp (Lean.mkConst ``List [0]) rowList else rowList
  unless ← isDefEq (← inferType value) expected do
    throwErrorAt input "boundary hints expected List Row or List (List Row)"
  let reduced ← withTransparency .all do
    reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)
  let mut result : Array Row := #[]
  for item in ← readList reduced do
    if nested then
      for row in ← readList item do
        result := result.push (← readRow row)
    else
      result := result.push (← readRow item)
    if result.size > 128 then
      throwErrorAt input "boundary hints total row limit exceeded (128)"
  return result

private def findHint (base : Array Row) (boundary : Row) : Option LineExclusion := Id.run do
  let pivot := if boundary.x = 0 then boundary.y else boundary.x
  if pivot = 0 then return none
  let scale : Int := pivot.natAbs
  for (row, i) in base.toList.zipIdx do
    let component := if boundary.x = 0 then row.y else row.x
    let multiple := if 0 ≤ pivot then component else -component
    if scale * row.x = multiple * boundary.x ∧
       scale * row.y = multiple * boundary.y ∧
       scale * row.constant < multiple * boundary.constant then
      return some ⟨i, scale, multiple⟩
  return none

private def construct (source forbidden : Syntax) :
    TermElabM (Array (Option LineExclusion) × Array Row) := do
  let base ← closedRows source false
  let other ← closedRows forbidden true
  if base.size > 64 || base.size + other.size > 128 then
    throwError "boundary hints require at most 64 base and 128 total rows"
  -- List.dedup keeps the last occurrence; preserve its exact boundary order.
  let mut reversed : Array Row := #[]
  for row in (base ++ other).reverse do
    unless reversed.any (fun previous => decide (previous = row)) do
      reversed := reversed.push row
  let mut plan : Array (Option LineExclusion) := #[]
  let mut active : Array Row := #[]
  for boundary in reversed.reverse do
    let hint := findHint base boundary
    plan := plan.push hint
    if hint.isNone then active := active.push boundary
  return (plan, active)

private def intExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkNatLit n)

private def rowExpr (row : Row) : Expr :=
  mkApp4 (Lean.mkConst ``Row.mk) (intExpr row.x) (intExpr row.y)
    (intExpr row.constant) (Lean.mkConst (if row.strict then ``Bool.true else ``Bool.false))

private def hintExpr : Option LineExclusion → Expr
  | none => mkApp (Lean.mkConst ``Option.none [0]) (Lean.mkConst ``LineExclusion)
  | some hint =>
      mkApp2 (Lean.mkConst ``Option.some [0]) (Lean.mkConst ``LineExclusion)
        (mkApp3 (Lean.mkConst ``LineExclusion.mk) (mkNatLit hint.baseIndex)
          (intExpr hint.scale) (intExpr hint.multiple))

private def listExpr (type : Expr) (items : Array Expr) : Expr := Id.run do
  let mut value := mkApp (Lean.mkConst ``List.nil [0]) type
  let cons := mkApp (Lean.mkConst ``List.cons [0]) type
  for item in items.reverse do value := mkApp2 cons item value
  return value

syntax "boundary_plan%(" term "," term ")" : term
syntax "boundary_rows%(" term "," term ")" : term

elab_rules : term
  | `(boundary_plan%($base:term, $forbidden:term)) => do
      let (plan, _) ← construct base forbidden
      return listExpr (mkApp (Lean.mkConst ``Option [0]) (Lean.mkConst ``LineExclusion))
        (plan.map hintExpr)
  | `(boundary_rows%($base:term, $forbidden:term)) => do
      let (_, rows) ← construct base forbidden
      return listExpr (Lean.mkConst ``Row) (rows.map rowExpr)

end N12Compact.BoundaryHintSyntax

namespace N12Compact.PlanarBoundaryHints

/-- Synthesis chooses data; both acceptance proofs are ordinary kernel checks. -/
syntax "boundary_cache%(" term "," term ")" : term

macro_rules
  | `(boundary_cache%($base:term, $forbidden:term)) =>
    `(({ plan := boundary_plan%($base, $forbidden)
         plan_checked := by decide +kernel
         rows := boundary_rows%($base, $forbidden)
         rows_exact := by decide +kernel } : Cache $base $forbidden))

end N12Compact.PlanarBoundaryHints
