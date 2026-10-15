import Compact.Bridge.RelaxationTable
import Compact.Core.RowMaterializeSyntax

/-! Untrusted data synthesis for compact relaxation records.

This elaborator reads closed row constructors, searches only their small
local lists, and emits natural-number witness positions. It neither constructs
proofs nor evaluates a theorem. `Entry.Check` still checks every emitted hint
by ordinary integer kernel reduction. Failed synthesis is an elaboration error;
there is no arbitrary fallback witness and no unverified imported result.
-/

namespace N12Compact.RelaxationSyntax
open Lean Elab Term Meta IntegerSupport RelaxationHints

private def natural (value : Expr) : TermElabM Nat := do
  let some n := value.rawNatLit?
    | throwError "relaxation_hints% expected a natural-number constructor"
  return n

private def integer (value : Expr) : TermElabM Int := do
  if value.isAppOfArity ``Int.ofNat 1 then
    return Int.ofNat (← natural value.getAppArgs[0]!)
  else if value.isAppOfArity ``Int.negSucc 1 then
    return Int.negSucc (← natural value.getAppArgs[0]!)
  else
    throwError "relaxation_hints% expected an integer constructor"

private def row (value : Expr) : TermElabM Row := do
  unless value.isAppOfArity ``Row.mk 4 do
    throwError "relaxation_hints% expected an integer Row constructor"
  let args := value.getAppArgs
  let strict ← if args[3]!.isConstOf ``Bool.true then pure true
    else if args[3]!.isConstOf ``Bool.false then pure false
    else throwError "relaxation_hints% expected a literal strictness flag"
  return ⟨← integer args[0]!, ← integer args[1]!, ← integer args[2]!, strict⟩

private def rows (input : Syntax) : TermElabM (Array Row) := do
  let value ← instantiateMVars (← elabTermAndSynthesize input none)
  if value.hasMVar || value.hasFVar then
    throwErrorAt input "relaxation_hints% requires closed source and target rows"
  let expected := mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Row)
  unless ← isDefEq (← inferType value) expected do
    throwErrorAt input "relaxation_hints% expects List Row"
  let reduced ← withTransparency .all do
    reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)
  let mut cursor := reduced
  let mut result := #[]
  while cursor.isAppOfArity ``List.cons 3 do
    let args := cursor.getAppArgs
    result := result.push (← row args[1]!)
    if result.size > 64 then
      throwErrorAt input "relaxation_hints% local row limit exceeded (64)"
    cursor := args[2]!
  unless cursor.isAppOfArity ``List.nil 1 do
    throwErrorAt input "relaxation_hints% could not reduce the closed row list"
  return result

private def strictOK (target a b : Row) (left right slack : Int) : Bool :=
  !target.strict || decide (0 < slack) ||
    (decide (0 < left) && a.strict) || (decide (0 < right) && b.strict)

private def constantOK (target : Row) : Bool :=
  decide (target.x = 0 ∧ target.y = 0 ∧ 0 ≤ target.constant) &&
    (!target.strict || decide (0 < target.constant))

private def singleOK (source target : Row) : Bool :=
  let pivot := if source.x = 0 then source.y else source.x
  let component := if source.x = 0 then target.y else target.x
  let scale : Int := pivot.natAbs
  let weight := if pivot < 0 then -component else component
  let slack := scale * target.constant - weight * source.constant
  decide (0 < scale ∧ 0 ≤ weight ∧ 0 ≤ slack ∧
    weight * source.x = scale * target.x ∧ weight * source.y = scale * target.y) &&
    strictOK target source SparseInteger.zero weight 0 slack

private def pairOK (a b target : Row) : Bool :=
  let determinant := a.x * b.y - a.y * b.x
  let rawLeft := target.x * b.y - target.y * b.x
  let rawRight := a.x * target.y - a.y * target.x
  let left := if determinant < 0 then -rawLeft else rawLeft
  let right := if determinant < 0 then -rawRight else rawRight
  let scale : Int := determinant.natAbs
  let slack := scale * target.constant - left * a.constant - right * b.constant
  decide (0 < scale ∧ 0 ≤ left ∧ 0 ≤ right ∧ 0 ≤ slack) &&
    strictOK target a b left right slack

private def synthesize (sources : Array Row) (target : Row) : TermElabM Hint := do
  if constantOK target then return .constant
  let indexed := sources.toList.zipIdx
  for (source, i) in indexed do
    if source = target then return .copy i
  for (source, i) in indexed do
    if singleOK source target then return .single i
  for (left, i) in indexed do
    for (right, j) in indexed do
      if i < j then
        if pairOK left right target then return .pair i j
  throwError "relaxation_hints% found no constant/one-row/two-row witness for target ({target.x}, {target.y}, {target.constant}, strict={target.strict}); preserve an explicit higher-arity certificate or simplify this obligation"

private def hintExpr : Hint → Expr
  | .constant => Lean.mkConst ``Hint.constant
  | .copy i => mkApp (Lean.mkConst ``Hint.copy) (mkNatLit i)
  | .single i => mkApp (Lean.mkConst ``Hint.single) (mkNatLit i)
  | .pair i j => mkApp2 (Lean.mkConst ``Hint.pair) (mkNatLit i) (mkNatLit j)

syntax "relaxation_hints%(" term "," term ")" : term

elab_rules : term
  | `(relaxation_hints%($source:term, $target:term)) => do
      let sources ← rows source
      let targets ← rows target
      -- A fixed local effort cap complements the parent's aggregate guard.
      if sources.size * sources.size * targets.size > 32768 then
        throwError "relaxation_hints% candidate bound exceeds 32768; provide audited hints explicitly"
      let mut hints : Array Expr := #[]
      for target in targets do
        hints := hints.push (hintExpr (← synthesize sources target))
      let type := Lean.mkConst ``Hint
      let cons := mkApp (Lean.mkConst ``List.cons [0]) type
      let mut result := mkApp (Lean.mkConst ``List.nil [0]) type
      for hint in hints.reverse do
        result := mkApp2 cons hint result
      return result

end N12Compact.RelaxationSyntax

namespace N12Compact.RelaxationTable
open IntegerSupport

/-- One semantic source record. Both row caches retain exact kernel-checked
bindings to the original dictionary. Witness search emits only data; callers
must separately prove the resulting entry's complete `Check`. -/
syntax "cached_relaxation%(" term "," term "," term ")" : term

macro_rules
  | `(cached_relaxation%($dictionary:term, $source:term, $target:term)) =>
    `(({ spec := ⟨$source, $target⟩
         inputs := materialize_rows% (($dictionary).poseRows $source).map ($dictionary).rows
         targets := materialize_rows% (($dictionary).poseRows $target).map ($dictionary).rows
         inputs_exact := by decide +kernel
         targets_exact := by decide +kernel
         hints := relaxation_hints%(
           (($dictionary).poseRows $source).map ($dictionary).rows,
           (($dictionary).poseRows $target).map ($dictionary).rows)
       } : Entry $dictionary))

end N12Compact.RelaxationTable
