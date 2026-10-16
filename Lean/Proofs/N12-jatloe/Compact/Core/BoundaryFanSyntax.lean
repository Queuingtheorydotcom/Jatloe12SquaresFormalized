import Compact.Core.VertexFanTable
import Compact.Core.VertexFromRows
import Compact.Core.RawSupportFan
import Lean.Elab.Term
import Lean.Meta.Reduce

/-! A support boundary stores its actual row IDs once in cyclic order.

Adjacent row pairs, primitive intersection coordinates and angular lookup
starts are derived. The cycle and angular order are untrusted choices: the
ordinary `RawContext.Check` still checks input membership and both exact
vertex equations, and every pair still checks all eight actual cones and
strict support inequalities. Degenerate contexts may retain the previous
explicit fan or a separately checked empty certificate.
-/

set_option Elab.async false

namespace N12Compact.BoundaryFan
open IntegerSupport ReferenceAxis CachedSupportFan VertexFanTable

/-- Polar comparison without rational division or trigonometric evaluation.
It is used only to choose lookup hints, never as a geometric premise. -/
def half (x y : Int) : Nat := if 0 < y ∨ (y = 0 ∧ 0 ≤ x) then 0 else 1

def before (a b : Direction) : Bool :=
  decide (half a.x a.y < half b.x b.y ∨
    (half a.x a.y = half b.x b.y ∧ 0 < a.x * b.y - a.y * b.x))

def lowerBound (directions : Array Direction) (normal : Direction) :
    Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match directions[mid]? with
        | none => lo
        | some candidate =>
            if before candidate normal then lowerBound directions normal fuel (mid + 1) hi
            else lowerBound directions normal fuel lo mid
      else lo

/-- One copy of each actual boundary row replaces separate first/second IDs,
start keys and vertex coordinates in every support entry. -/
def cycleEntries {r : Nat} (rows : Fin r → Row) (directions : Array Direction)
    (cycle : List (Fin r)) : Array (CachedSupportFan.Entry r) :=
  let pairs := cycle.zip (cycle.drop 1 ++ cycle.take 1)
  let entries := pairs.map fun pair =>
    let first := rows pair.1
    let second := rows pair.2
    let start := lowerBound directions ⟨first.x, first.y, 1⟩ 16 0 directions.size
    (⟨start, pair.1, pair.2, VertexSupport.Basis.fromRowsPrimitive first second⟩ :
      CachedSupportFan.Entry r)
  match entries.reverse with
  | [] => #[]
  | last :: _ => ({ last with start := 0 } :: entries).toArray

def context {r : Nat} (rows : Fin r → Row) (inputs : List (Fin r))
    (reference : Reference) (directions : Array Direction) (cycle : List (Fin r)) :
    RawContext r :=
  ⟨inputs, reference, cycleEntries rows directions cycle⟩

end N12Compact.BoundaryFan

namespace N12Compact.BoundaryFanSyntax
open Lean Elab Term Meta

/-- Emit closed constructor data. This notation supplies no proof: the caller
must prove the standard context check and every actual pair check afterward. -/
syntax (name := materializeBoundaryFan) "materialize_boundary_fan% " term : term

elab_rules : term
  | `(materialize_boundary_fan% $input:term) => do
      let value ← instantiateMVars (← elabTermAndSynthesize input none)
      if value.hasMVar || value.hasFVar then
        throwErrorAt input "materialize_boundary_fan% requires a closed concrete context"
      let type ← whnf (← inferType value)
      unless type.isAppOfArity ``VertexFanTable.RawContext 1 do
        throwErrorAt input "materialize_boundary_fan% expects VertexFanTable.RawContext"
      withTransparency .all do
        reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)

/-- Materialize the numeric view once, removing dictionaries and certified
entries from subsequent numeric reduction. An ordinary equality to
`CachedSupportFan.Context.numeric` must accompany this cache before soundness
can be transferred with `Context.cached_numeric_valid`. -/
syntax (name := materializeRawFan) "materialize_raw_fan% " term : term

elab_rules : term
  | `(materialize_raw_fan% $input:term) => do
      let value ← instantiateMVars (← elabTermAndSynthesize input none)
      if value.hasMVar || value.hasFVar then
        throwErrorAt input "materialize_raw_fan% requires a closed concrete numeric context"
      unless ← isDefEq (← inferType value) (Lean.mkConst ``RawSupportFan.Context) do
        throwErrorAt input "materialize_raw_fan% expects RawSupportFan.Context"
      withTransparency .all do
        reduce value (explicitOnly := true) (skipTypes := true) (skipProofs := true)

end N12Compact.BoundaryFanSyntax
