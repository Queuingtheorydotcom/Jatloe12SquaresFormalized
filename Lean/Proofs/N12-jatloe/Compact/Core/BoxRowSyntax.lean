import Compact.Core.BoxRowRecipe
import Compact.Core.SparseLiteral

/-! A box line supplies four original IDs and four geometric bounds.  The
elaborator calls the exact BoxRowRecipe decoder, then materializes ordinary
Row/Int/Prod/tree constructors. Lookup and numerical checking therefore have
the same kernel data representation as sparse_rows%, with no extra index
table, box lookup, runtime division, oracle, or proof-producing evaluator.

Raw row:  originalID:x,y,constant,strict,denominatorPred
Box:      B:leftID,rightID,bottomID,topID;n,d|n,d|n,d|n,d;strictMask
The mask uses bits 0..3 in that face order. Each d stores denominator minus 1.
-/
namespace N12Compact.BoxRowSyntax
open Lean Elab Term IntegerSupport BoxRowRecipe

syntax (name := boxedSparseRows) "boxed_sparse_rows% " str : term

private def integerExpr : Int → Expr
  | .ofNat n => mkApp (Lean.mkConst ``Int.ofNat) (mkNatLit n)
  | .negSucc n => mkApp (Lean.mkConst ``Int.negSucc) (mkNatLit n)

private def rowType : Expr :=
  mkApp2 (Lean.mkConst ``Prod [0, 0]) (Lean.mkConst ``Row) (Lean.mkConst ``Nat)

private def pairExpr (value : Row × Nat) : Expr :=
  let r := value.1
  let row := mkApp4 (Lean.mkConst ``Row.mk) (integerExpr r.x) (integerExpr r.y)
    (integerExpr r.constant) (Lean.mkConst (if r.strict then ``Bool.true else ``Bool.false))
  mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) (Lean.mkConst ``Row) (Lean.mkConst ``Nat)
    row (mkNatLit value.2)

private def balanced (entries : Array (Nat × Expr)) : Expr := Id.run do
  let empty := mkApp (Lean.mkConst ``SparseLiteral.Tree.empty) rowType
  let rec build : Nat → Nat → Nat → Expr
    | 0, _, _ => empty
    | fuel+1, lo, hi =>
        if lo >= hi then empty else
        let mid := (lo+hi)/2
        let entry := entries[mid]!
        mkApp5 (Lean.mkConst ``SparseLiteral.Tree.node) rowType
          (mkNatLit entry.1) entry.2 (build fuel lo mid) (build fuel (mid+1) hi)
  build entries.size 0 entries.size

private def natField (ref : Syntax) (text : String) : TermElabM Nat := do
  let some value := text.trimAscii.toString.toNat? | throwErrorAt ref "expected natural number"
  return value

private def intField (ref : Syntax) (text : String) : TermElabM Int := do
  let some value := text.trimAscii.toString.toInt? | throwErrorAt ref "expected integer numerator"
  return value

private def boolField (ref : Syntax) (text : String) : TermElabM Bool :=
  match text.trimAscii.toString with
  | "false" => pure false
  | "true" => pure true
  | _ => throwErrorAt ref "expected strictness true or false"

elab_rules : term
  | `(boxed_sparse_rows% $text:str) => do
      let mut entries : Array (Nat × Expr) := #[]
      for raw in text.getString.splitOn "\n" do
        let line := raw.trimAscii.toString
        if !line.isEmpty then
          let [kind, payload] := line.splitOn ":"
            | throwErrorAt text "expected originalID:row or B:box"
          if kind == "B" then
            let [keys, bounds, strict] := payload.splitOn ";"
              | throwErrorAt text "box expects IDs;bounds;strictMask"
            let keys ← (keys.splitOn ",").mapM (natField text)
            let fields := bounds.splitOn "|"
            unless keys.length == 4 && fields.length == 4 do
              throwErrorAt text "box needs exactly four IDs and bounds"
            let mask ← natField text strict
            unless mask < 16 do throwErrorAt text "strictMask must be below 16"
            let faces := [Face.left, Face.right, Face.bottom, Face.top]
            for index in [:4] do
              let [numerator, denominatorPred] := fields[index]!.splitOn ","
                | throwErrorAt text "bound expects numerator,denominatorPred"
              let bound : Bound := ⟨← intField text numerator,
                ← natField text denominatorPred, mask.testBit index⟩
              entries := entries.push (keys[index]!, pairExpr (bound.row faces[index]!))
          else
            let key ← natField text kind
            let [x,y,c,s,d] := payload.splitOn ","
              | throwErrorAt text "raw row expects five fields"
            let row : Row := ⟨← intField text x, ← intField text y,
              ← intField text c, ← boolField text s⟩
            entries := entries.push (key, pairExpr (row, ← natField text d))
      entries := entries.qsort (fun a b => a.1 < b.1)
      for i in [:entries.size-1] do
        unless entries[i]!.1 < entries[i+1]!.1 do
          throwErrorAt text "duplicate original row ID"
      return balanced entries

private def sample := boxed_sparse_rows% "
B:2,19,3,101;1,1|7,2|5,3|9,4;5
80:3,-7,2,true,15
"

example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 2 =
    (⟨2,0,-1,true⟩,1) := rfl
example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 19 =
    (⟨-3,0,7,false⟩,2) := rfl
example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 3 =
    (⟨0,4,-5,true⟩,3) := rfl
example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 101 =
    (⟨0,-5,9,false⟩,4) := rfl

end N12Compact.BoxRowSyntax
