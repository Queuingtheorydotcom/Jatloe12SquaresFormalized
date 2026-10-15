import Compact.Core.RowSyntax

/-! Typed pose dictionaries. Literal Fin bounds are proved by ordinary kernel
reduction of Nat.decLt; the parser supplies no unchecked proof or native oracle. -/

namespace N12Compact.PoseSyntax
open Lean Elab Term

syntax (name := poseText) "pose_text% " num num str : term

private def finExpr (bound value : Nat) : Expr :=
  let n := mkNatLit bound
  let i := mkNatLit value
  let proposition := mkApp2 (Lean.mkConst ``Nat.lt) i n
  let decision := mkApp2 (Lean.mkConst ``Nat.decLt) i n
  let proof := mkApp3 (Lean.mkConst ``of_decide_eq_true) proposition decision reflBoolTrue
  mkApp3 (Lean.mkConst ``Fin.mk) n i proof

private def listExpr (elementType : Expr) (entries : Array Expr) : Expr := Id.run do
  let cons := mkApp (Lean.mkConst ``List.cons [0]) elementType
  let mut result := mkApp (Lean.mkConst ``List.nil [0]) elementType
  for entry in entries.reverse do
    result := mkApp2 cons entry result
  return result

private def arrayExpr (elementType : Expr) (entries : Array Expr) : Expr :=
  mkApp2 (Lean.mkConst ``Array.mk [0]) elementType (listExpr elementType entries)

elab_rules : term
  | `(pose_text% $angleBound:num $rowBound:num $text:str) => do
      let a := angleBound.getNat
      let r := rowBound.getNat
      let angleType := mkApp (Lean.mkConst ``Fin) (mkNatLit a)
      let rowType := mkApp (Lean.mkConst ``Fin) (mkNatLit r)
      let rowsType := mkApp (Lean.mkConst ``List [0]) rowType
      let poseType := mkApp2 (Lean.mkConst ``Prod [0, 0]) angleType rowsType
      let mut rowCache : Std.HashMap Nat Expr := {}
      let mut chunks : Array Expr := #[]
      let mut chunk : Array Expr := #[]
      let mut lineNumber : Nat := 0
      for line in text.getString.splitOn "\n" do
        lineNumber := lineNumber + 1
        let line := line.trim
        if !line.isEmpty then
          let [angle, rowList] := line.splitOn ";"
            | throwErrorAt text "pose {lineNumber}: expected angle;row-list"
          let some angle := angle.trim.toNat?
            | throwErrorAt text "pose {lineNumber}: invalid angle integer"
          unless angle < a do throwErrorAt text "pose {lineNumber}: angle exceeds its bound"
          let mut rows : Array Expr := #[]
          if !rowList.trim.isEmpty then
            for field in rowList.splitOn "," do
              let some row := field.trim.toNat?
                | throwErrorAt text "pose {lineNumber}: invalid row index"
              unless row < r do throwErrorAt text "pose {lineNumber}: row exceeds its bound"
              let value := match rowCache[row]? with
                | some value => value
                | none => finExpr r row
              rowCache := rowCache.insert row value
              rows := rows.push value
          let value := mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) angleType rowsType
            (finExpr a angle) (listExpr rowType rows)
          chunk := chunk.push value
          if chunk.size = 256 then
            chunks := chunks.push (arrayExpr poseType chunk)
            chunk := #[]
      if !chunk.isEmpty then chunks := chunks.push (arrayExpr poseType chunk)
      return arrayExpr (mkApp (Lean.mkConst ``Array [0]) poseType) chunks

def lookup {a r : Nat} (chunks : Array (Array (Fin a × List (Fin r))))
    (fallback : Fin a × List (Fin r)) (index : Nat) : Fin a × List (Fin r) :=
  (((chunks[index / 256]?).getD #[])[index % 256]?).getD fallback

example : lookup (pose_text% 64 26026 "
0;0,1,26025
63;
") (0, []) 0 = (0, [0, 1, 26025]) := rfl
example : lookup (pose_text% 64 26026 "63;") (0, []) 0 = (63, []) := rfl

end N12Compact.PoseSyntax
