import Compact.Core.PoseSyntax

/-! Sparse transparent dictionaries preserve their external natural-number
indices. A missing key returns the caller's explicit fallback. The literal
elaborators emit ordinary balanced constructor trees; the kernel checks the
resulting values. No executable evaluator or proof oracle is used. -/

namespace N12Compact.SparseLiteral

inductive Tree (α : Type) where
  | empty
  | node (key : Nat) (value : α) (left right : Tree α)

def lookup {α : Type} (fallback : α) : Tree α → Nat → α
  | .empty, _ => fallback
  | .node key value left right, query =>
      if query < key then lookup fallback left query
      else if key < query then lookup fallback right query
      else value

open Lean Elab Term

syntax (name := sparseRows) "sparse_rows% " str : term
syntax (name := sparsePoses) "sparse_poses% " num num str : term
syntax (name := sparseRowsSubset) "sparse_rows_subset% " ident str : term

private def arrayExpr (type : Expr) (values : Array Expr) : Expr := Id.run do
  let cons := mkApp (Lean.mkConst ``List.cons [0]) type
  let mut list := mkApp (Lean.mkConst ``List.nil [0]) type
  for value in values.reverse do list := mkApp2 cons value list
  return mkApp2 (Lean.mkConst ``Array.mk [0]) type list

private def rowType : Expr :=
  mkApp2 (Lean.mkConst ``Prod [0, 0])
    (Lean.mkConst ``IntegerSupport.Row) (Lean.mkConst ``Nat)

private def literalNat? (value : Expr) : Option Nat :=
  let value := value.consumeMData
  if let some n := value.rawNatLit? then some n
  else if value.isAppOfArity ``OfNat.ofNat 3 then
    let args := value.getAppArgs
    if args[0]!.consumeMData.isConstOf ``Nat then args[1]!.consumeMData.rawNatLit?
    else none
  else none

private def balancedExpr (type : Expr) (entries : Array (Nat × Expr)) : Expr :=
  let empty := mkApp (Lean.mkConst ``Tree.empty) type
  let rec build : Nat → Nat → Nat → Expr
    | 0, _, _ => empty
    | fuel + 1, lo, hi =>
        if lo >= hi then empty else
        let mid := (lo + hi) / 2
        let entry := entries[mid]!
        mkApp5 (Lean.mkConst ``Tree.node) type (mkRawNatLit entry.1) entry.2
          (build fuel lo mid) (build fuel (mid + 1) hi)
  build entries.size 0 entries.size

private def literalArray (value : Expr) : TermElabM (Array Expr) := do
  unless value.isAppOfArity ``Array.mk 2 do
    throwError "sparse literal expects an explicit Array.mk constructor"
  let mut list := value.getAppArgs[1]!
  let mut entries := #[]
  while list.isAppOfArity ``List.cons 3 do
    let args := list.getAppArgs
    entries := entries.push args[1]!
    list := args[2]!
  unless list.isAppOfArity ``List.nil 1 do
    throwError "sparse literal expects an explicit List.cons spine"
  return entries

/-- Parse indices separately, then let the existing typed row/pose elaborator
construct each payload. Strictly increasing keys make the search layout exact. -/
private def splitKeys (text : TSyntax `str) : TermElabM (Array Nat × String) := do
  let mut keys := #[]
  let mut payloads : Array String := #[]
  for raw in text.getString.splitOn "\n" do
    let line := raw.trim
    if !line.isEmpty then
      let fields := line.splitOn ":"
      let [key, payload] := fields
        | throwErrorAt text "sparse literal expects original-index:payload"
      let some key := key.trim.toNat?
        | throwErrorAt text "sparse literal index must be a natural number"
      if let some previous := keys.back? then
        unless previous < key do
          throwErrorAt text "sparse literal indices must be strictly increasing"
      keys := keys.push key
      payloads := payloads.push payload
  return (keys, String.intercalate "\n" payloads.toList)

private def fromChunks (type : Expr) (keys : Array Nat) (value : Expr) : TermElabM Expr := do
  let chunks ← literalArray value
  let mut entries : Array (Nat × Expr) := #[]
  for chunk in chunks do
    for entry in (← literalArray chunk) do
      let some key := keys[entries.size]?
        | throwError "sparse literal has more values than indices"
      entries := entries.push (key, entry)
  unless entries.size = keys.size do
    throwError "sparse literal has fewer values than indices"
  return balancedExpr type entries

elab_rules : term
  | `(sparse_rows% $text:str) => do
      let (keys, payload) ← splitKeys text
      let payload := Syntax.mkStrLit payload
      let value ← elabTerm (← `(row_text% $payload:str)) none
      fromChunks rowType keys value
  | `(sparse_poses% $angles:num $rows:num $text:str) => do
      let (keys, payload) ← splitKeys text
      let payload := Syntax.mkStrLit payload
      let value ← elabTerm (← `(pose_text% $angles:num $rows:num $payload:str)) none
      let type := mkApp2 (Lean.mkConst ``Prod [0, 0])
        (mkApp (Lean.mkConst ``Fin) (mkNatLit angles.getNat))
        (mkApp (Lean.mkConst ``List [0])
          (mkApp (Lean.mkConst ``Fin) (mkNatLit rows.getNat)))
      fromChunks type keys value
  | `(sparse_rows_subset% $table:ident $indices:str) => do
      let tableExpr ← elabTerm table none
      let .const name _ := tableExpr
        | throwErrorAt table "sparse_rows_subset% expects a named literal definition"
      let .defnInfo info ← getConstInfo name
        | throwErrorAt table "sparse_rows_subset% expects a transparent literal definition"
      let mut stack := #[info.value]
      let mut values : Std.HashMap Nat Expr := {}
      while !stack.isEmpty do
        let current := stack.back!.consumeMData
        stack := stack.pop
        if current.isAppOfArity ``Tree.empty 1 then pure ()
        else if current.isAppOfArity ``Tree.node 5 then
          let args := current.getAppArgs
          let some key := literalNat? args[1]!
            | throwErrorAt table "sparse tree key must be a literal natural number; found {repr args[1]!}"
          unless !(values.contains key) do
            throwErrorAt table "sparse tree contains a duplicate key"
          values := values.insert key args[2]!
          stack := stack.push args[3]! |>.push args[4]!
        else throwErrorAt table "sparse_rows_subset% expects literal tree constructors"
      let mut chunks : Array Expr := #[]
      let mut chunk : Array Expr := #[]
      if !indices.getString.trim.isEmpty then
        for field in indices.getString.splitOn "," do
          let some key := field.trim.toNat?
            | throwErrorAt indices "sparse subset index must be a natural number"
          let some value := values[key]?
            | throwErrorAt indices "sparse subset index {key} is absent"
          chunk := chunk.push value
          if chunk.size = 256 then
            chunks := chunks.push (arrayExpr rowType chunk)
            chunk := #[]
      if !chunk.isEmpty then chunks := chunks.push (arrayExpr rowType chunk)
      return arrayExpr (mkApp (Lean.mkConst ``Array [0]) rowType) chunks

private def exampleRows := sparse_rows% "
2:3,-7,2,true,15
19:-1,0,9,false,0
100000:0,1,-4,false,9
"

example : lookup (⟨0,0,0,false⟩,0) exampleRows 19 =
    (⟨-1,0,9,false⟩,0) := rfl
example : lookup (⟨0,0,0,false⟩,0) exampleRows 3 =
    (⟨0,0,0,false⟩,0) := rfl
example : RowSyntax.lookup (sparse_rows_subset% exampleRows "19,2,19") 1 =
    lookup (⟨0,0,0,false⟩,0) exampleRows 2 := rfl
example : lookup (0, []) (sparse_poses% 64 26026 "19:63;0,26025") 19 =
    ((63 : Fin 64), [0, 26025]) := rfl

end N12Compact.SparseLiteral
