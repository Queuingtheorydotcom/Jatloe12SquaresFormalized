import Compact.Core.CachedSupportFan

/-!
The intersection of two nonparallel input rows is algebraically determined.
A fan therefore needs no independently supplied vertex coordinates or copied
row coefficients. This constructor preserves both original strictness bits.

The cached interface remains useful for numeric replay: callers may materialize
`IndexedEntry.expand` once and certify the equality before pair checks. They
must not repeatedly unfold a large global row dictionary during those checks.
-/

set_option Elab.async false

namespace N12Compact.VertexSupport

open IntegerSupport

def rowDeterminant (a b : Row) : Int := a.x * b.y - a.y * b.x

/-- An exact intersection with positive denominator whenever the two row
normals are independent. No division, rational computation or witness is used. -/
def Basis.fromRows (a b : Row) : Basis :=
  let d := rowDeterminant a b
  let x := a.y * b.constant - a.constant * b.y
  let y := a.constant * b.x - a.x * b.constant
  if d < 0 then ⟨a, b, -x, -y, -d⟩ else ⟨a, b, x, y, d⟩

/-- Deterministic primitive coordinates for smaller numeric replay. This is a
data constructor, not a proof: callers independently establish `Basis.Check`
after materialization, including positive denominator and both equations. -/
def Basis.primitive (basis : Basis) : Basis :=
  let divisor : Int := basis.x.natAbs.gcd (basis.y.natAbs.gcd basis.denominator.natAbs)
  ⟨basis.first, basis.second, basis.x / divisor, basis.y / divisor,
    basis.denominator / divisor⟩

def Basis.fromRowsPrimitive (a b : Row) : Basis := (Basis.fromRows a b).primitive

theorem Basis.fromRows_checked (a b : Row) (independent : rowDeterminant a b ≠ 0) :
    (Basis.fromRows a b).Check := by
  by_cases negative : rowDeterminant a b < 0
  · simp only [fromRows, negative, ↓reduceIte, Check]
    refine ⟨neg_pos.mpr negative, ?_, ?_⟩ <;>
      dsimp [rowDeterminant] <;> ring
  · have positive : 0 < rowDeterminant a b :=
      lt_of_le_of_ne (le_of_not_gt negative) (Ne.symm independent)
    simp only [fromRows, negative, ↓reduceIte, Check]
    refine ⟨positive, ?_, ?_⟩ <;> dsimp [rowDeterminant] <;> ring

@[simp] theorem Basis.fromRows_first (a b : Row) : (Basis.fromRows a b).first = a := by
  dsimp only [fromRows]
  split <;> rfl

@[simp] theorem Basis.fromRows_second (a b : Row) : (Basis.fromRows a b).second = b := by
  dsimp only [fromRows]
  split <;> rfl

end N12Compact.VertexSupport

namespace N12Compact.CachedSupportFan

open IntegerSupport VertexSupport

/-- Only a lookup key and the actual two input indices are independent data. -/
structure IndexedEntry (r : Nat) where
  start : Nat
  first : Fin r
  second : Fin r

def IndexedEntry.Check {r : Nat} (rows : Fin r → Row) (inputs : List (Fin r))
    (entry : IndexedEntry r) : Prop :=
  entry.first ∈ inputs ∧ entry.second ∈ inputs ∧
    rowDeterminant (rows entry.first) (rows entry.second) ≠ 0

instance {r : Nat} (rows : Fin r → Row) (inputs : List (Fin r))
    (entry : IndexedEntry r) : Decidable (entry.Check rows inputs) :=
  inferInstanceAs (Decidable (_ ∧ _))

def IndexedEntry.expand {r : Nat} (rows : Fin r → Row) (entry : IndexedEntry r) :
    Entry r :=
  ⟨entry.start, entry.first, entry.second,
    Basis.fromRows (rows entry.first) (rows entry.second)⟩

theorem IndexedEntry.expand_checked {r : Nat} (rows : Fin r → Row)
    (inputs : List (Fin r)) (entry : IndexedEntry r) (checked : entry.Check rows inputs) :
    (entry.expand rows).Check rows inputs := by
  refine ⟨checked.1, checked.2.1, ?_, ?_, ?_⟩
  · exact Basis.fromRows_first _ _
  · exact Basis.fromRows_second _ _
  · exact Basis.fromRows_checked _ _ checked.2.2

/-- A cached expansion is sound only after its equality to the indexed data
has been checked. Elaborator-side normalization is not a trusted premise. -/
theorem IndexedEntry.cached_checked {r : Nat} (rows : Fin r → Row)
    (inputs : List (Fin r)) (entry : IndexedEntry r) (cached : Entry r)
    (equal : cached = entry.expand rows) (checked : entry.Check rows inputs) :
    cached.Check rows inputs := by
  rw [equal]
  exact entry.expand_checked rows inputs checked

#print axioms IndexedEntry.expand_checked

end N12Compact.CachedSupportFan
