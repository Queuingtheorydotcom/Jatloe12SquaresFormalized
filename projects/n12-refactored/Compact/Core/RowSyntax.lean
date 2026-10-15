import Compact.Core.IntegerSupport
import Lean.Elab.Term

/-!
Transparent row literals without per-entry typeclass synthesis.

This elaborator reads only the literal syntax below and constructs ordinary
`Row.mk`, integer constructors, `Prod.mk`, `List.cons`, and `Array.mk` terms.
The resulting definition is checked by Lean's kernel exactly as any other
transparent array definition. There is no file access, oracle, evaluation of
proof claims, new axiom, or unsafe cast.
-/

namespace N12Compact.RowSyntax
open Lean Elab Term

/-- Signed decimal integer syntax, deliberately excluding arbitrary terms. -/
declare_syntax_cat rowInt
syntax num : rowInt
syntax "-" num : rowInt

declare_syntax_cat rowBool
syntax ident : rowBool

/-- `(x, y, constant, strict, stored denominator)` in the original row order. -/
declare_syntax_cat rowEntry
syntax "(" rowInt "," rowInt "," rowInt "," rowBool "," num ")" : rowEntry
syntax (name := rowArray) "row_array%[" withoutPosition(rowEntry,*,?) "]" : term
syntax (name := rowChunks) "row_chunks%[" withoutPosition(rowEntry,*,?) "]" : term
syntax (name := rowText) "row_text% " str : term

private def integerExpr (s : Syntax) : TermElabM Expr := do
  match s with
  | `(rowInt| $n:num) =>
      return mkApp (Lean.mkConst ``Int.ofNat) (mkNatLit n.getNat)
  | `(rowInt| -$n:num) =>
      match n.getNat with
      | 0 => return mkApp (Lean.mkConst ``Int.ofNat) (mkNatLit 0)
      | k + 1 => return mkApp (Lean.mkConst ``Int.negSucc) (mkNatLit k)
  | _ => throwErrorAt s "expected a signed decimal integer literal"

private def booleanExpr (s : Syntax) : TermElabM Expr := do
  match s with
  | `(rowBool| $value:ident) =>
      if value.getId == `true then return Lean.mkConst ``Bool.true
      else if value.getId == `false then return Lean.mkConst ``Bool.false
      else throwErrorAt value "expected true or false"
  | _ => throwErrorAt s "expected true or false"

private def entryExpr (s : Syntax) : TermElabM Expr := do
  match s with
  | `(rowEntry| ($x:rowInt, $y:rowInt, $c:rowInt, $strict:rowBool, $den:num)) =>
      let row := mkApp4 (Lean.mkConst ``IntegerSupport.Row.mk)
        (← integerExpr x) (← integerExpr y) (← integerExpr c) (← booleanExpr strict)
      return mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
        (Lean.mkConst ``IntegerSupport.Row) (Lean.mkConst ``Nat) row (mkNatLit den.getNat)
  | _ => throwErrorAt s "expected a five-field row literal"

private def arrayExpr (elementType : Expr) (entries : Array Expr) : Expr := Id.run do
  let cons := mkApp (Lean.mkConst ``List.cons [0]) elementType
  let mut result := mkApp (Lean.mkConst ``List.nil [0]) elementType
  for entry in entries.reverse do
    result := mkApp2 cons entry result
  return mkApp2 (Lean.mkConst ``Array.mk [0]) elementType result

private def rowPairType : Expr :=
  mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``IntegerSupport.Row) (Lean.mkConst ``Nat)

private def intValueExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkNatLit n)

private def textEntryExpr (ref : Syntax) (line : String) (lineNumber : Nat) : TermElabM Expr := do
  let [x, y, c, strict, den] := line.splitOn ","
    | throwErrorAt ref "row {lineNumber}: expected five comma-separated fields"
  let some x := x.trim.toInt? | throwErrorAt ref "row {lineNumber}: invalid x integer"
  let some y := y.trim.toInt? | throwErrorAt ref "row {lineNumber}: invalid y integer"
  let some c := c.trim.toInt? | throwErrorAt ref "row {lineNumber}: invalid constant integer"
  let strict ← match strict.trim with
    | "true" => pure (Lean.mkConst ``Bool.true)
    | "false" => pure (Lean.mkConst ``Bool.false)
    | _ => throwErrorAt ref "row {lineNumber}: expected true or false"
  let some den := den.trim.toNat? | throwErrorAt ref "row {lineNumber}: invalid natural denominator"
  let row := mkApp4 (Lean.mkConst ``IntegerSupport.Row.mk)
    (intValueExpr x) (intValueExpr y) (intValueExpr c) strict
  return mkApp4 (Lean.mkConst ``Prod.mk [0, 0])
    (Lean.mkConst ``IntegerSupport.Row) (Lean.mkConst ``Nat) row (mkNatLit den)

elab_rules : term
  | `(row_array%[$entries:rowEntry,*]) => do
      let values ← entries.getElems.mapM fun entry => entryExpr entry
      return arrayExpr rowPairType values
  | `(row_chunks%[$entries:rowEntry,*]) => do
      let mut chunk : Array Expr := #[]
      let mut chunks : Array Expr := #[]
      for entry in entries.getElems do
        chunk := chunk.push (← entryExpr entry)
        if chunk.size = 256 then
          chunks := chunks.push (arrayExpr rowPairType chunk)
          chunk := #[]
      if !chunk.isEmpty then
        chunks := chunks.push (arrayExpr rowPairType chunk)
      return arrayExpr (mkApp (Lean.mkConst ``Array [0]) rowPairType) chunks
  | `(row_text% $text:str) => do
      let mut chunk : Array Expr := #[]
      let mut chunks : Array Expr := #[]
      let mut lineNumber := 0
      for line in text.getString.splitOn "\n" do
        lineNumber := lineNumber + 1
        let line := line.trim
        if !line.isEmpty then
          chunk := chunk.push (← textEntryExpr text line lineNumber)
          if chunk.size = 256 then
            chunks := chunks.push (arrayExpr rowPairType chunk)
            chunk := #[]
      if !chunk.isEmpty then
        chunks := chunks.push (arrayExpr rowPairType chunk)
      return arrayExpr (mkApp (Lean.mkConst ``Array [0]) rowPairType) chunks

/-- Bounded-depth storage with exact original global indexing. No flattening. -/
def lookup (chunks : Array (Array (IntegerSupport.Row × Nat))) (index : Nat) :
    IntegerSupport.Row × Nat :=
  (((chunks[index / 256]?).getD #[])[index % 256]?).getD (⟨0, 0, 0, false⟩, 0)

/-- Representative signs, large values, and empty tables reduce by reflexivity. -/
example : (row_array%[] : Array (IntegerSupport.Row × Nat)) = #[] := rfl
example : (row_array%[
    (1064896000, -68149184250, 33617341181, false, 68157503749),
    (-0, 0, -1, true, 0),
  ] : Array (IntegerSupport.Row × Nat)) = #[
    (⟨1064896000, -68149184250, 33617341181, false⟩, 68157503749),
    (⟨0, 0, -1, true⟩, 0)
  ] := rfl

example : (row_chunks%[] : Array (Array (IntegerSupport.Row × Nat))) = #[] := rfl
example : lookup row_chunks%[(3, -7, 2, true, 15)] 0 = (⟨3, -7, 2, true⟩, 15) := rfl
example : lookup row_chunks%[(3, -7, 2, true, 15)] 1 = (⟨0, 0, 0, false⟩, 0) := rfl

example : lookup (row_text% "
1064896000,-68149184250,33617341181,false,68157503749
0,0,-1,true,0
") 1 = (⟨0, 0, -1, true⟩, 0) := rfl

end N12Compact.RowSyntax
