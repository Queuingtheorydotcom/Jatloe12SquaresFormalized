import Compact.Core.StripRowRecipe
import Compact.Core.BoxRowSyntax

/-! Exact strip records share an original geometric normal. The existing
accepted box literal builds the ordinary row tree after the typed strip
decoder reconstructs its two original rows. No runtime arithmetic or index
table is added, and the decoder is not a proof oracle.

M:lowerID,upperID;x,y;lowerNumerator,upperNumerator;lowerDenPred,upperDenPred;mask
P:lowerID,upperID;x,y;lowerScale,upperScale;lowerNumerator,upperNumerator;lowerDenPred,upperDenPred;mask
Mask bits 0 and 1 retain lower/upper strictness. Raw rows and B boxes pass
unchanged to the accepted boxed_sparse_rows% syntax.
-/
namespace N12Compact.StripRowSyntax
open Lean Elab Term IntegerSupport StripRowRecipe

syntax (name := stripSparseRows) "strip_sparse_rows% " str : term

private def natField (ref : Syntax) (text : String) : TermElabM Nat := do
  let some n := text.trim.toNat? | throwErrorAt ref "expected natural number"
  return n

private def intField (ref : Syntax) (text : String) : TermElabM Int := do
  let some n := text.trim.toInt? | throwErrorAt ref "expected integer"
  return n

private def rowText (id : Nat) (value : Row × Nat) : String :=
  let r := value.1
  s!"{id}:{r.x},{r.y},{r.constant},{if r.strict then "true" else "false"},{value.2}"

elab_rules : term
  | `(strip_sparse_rows% $text:str) => do
      let mut lines : Array String := #[]
      for raw in text.getString.splitOn "\n" do
        let line := raw.trim
        if !line.isEmpty then
          let [kind, payload] := line.splitOn ":"
            | throwErrorAt text "expected row ID, B box, M strip or P strip"
          if kind == "M" || kind == "P" then
            let fields := payload.splitOn ";"
            let (ids,normal,scales,bounds,denominators,mask) ←
              if kind == "M" then
                match fields with
                | [ids,normal,bounds,denominators,mask] =>
                    pure (ids,normal,"1,1",bounds,denominators,mask)
                | _ => throwErrorAt text "M strip expects five fields"
              else
                match fields with
                | [ids,normal,scales,bounds,denominators,mask] =>
                    pure (ids,normal,scales,bounds,denominators,mask)
                | _ => throwErrorAt text "P strip expects six fields"
            let [lid,uid] := ids.splitOn "," | throwErrorAt text "expected two row IDs"
            let [x,y] := normal.splitOn "," | throwErrorAt text "expected normal x,y"
            let [lo,hi] := bounds.splitOn "," | throwErrorAt text "expected two bounds"
            let [ld,ud] := denominators.splitOn "," | throwErrorAt text "expected two denominators"
            let [ls,us] := scales.splitOn "," | throwErrorAt text "expected two positive scales"
            let ls ← natField text ls
            let us ← natField text us
            unless 0 < ls && 0 < us do throwErrorAt text "strip scales must be positive"
            let mask ← natField text mask
            unless mask < 4 do throwErrorAt text "strip strictness mask must be below four"
            let strip : Strip := ⟨← intField text x, ← intField text y, ls-1, us-1,
              ⟨← intField text lo, ← natField text ld, mask.testBit 0⟩,
              ⟨← intField text hi, ← natField text ud, mask.testBit 1⟩⟩
            lines := lines.push (rowText (← natField text lid) (strip.row .lower))
            lines := lines.push (rowText (← natField text uid) (strip.row .upper))
          else
            lines := lines.push line
      let literal := Syntax.mkStrLit (String.intercalate "\n" lines.toList)
      elabTerm (← `(boxed_sparse_rows% $literal:str)) none

private def sample := strip_sparse_rows% "
M:2,7;3,-5;4,9;6,8;1
P:10,19;2,3;7,11;13,17;20,22;2
"

example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 2 =
    (⟨3,-5,-4,true⟩,6) := rfl
example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 7 =
    (⟨-3,5,9,false⟩,8) := rfl
example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 10 =
    (⟨14,21,-13,false⟩,20) := rfl
example : SparseLiteral.lookup (⟨0,0,0,false⟩,0) sample 19 =
    (⟨-22,-33,17,true⟩,22) := rfl

end N12Compact.StripRowSyntax
