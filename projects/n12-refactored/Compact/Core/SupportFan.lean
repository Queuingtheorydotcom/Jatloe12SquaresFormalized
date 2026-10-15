import Compact.Core.PairSupportFast
import Compact.Core.PairPruning

/-!
A support fan stores direction breakpoints and pairs of input-row indices.
Lookup is a bounded binary search, not a search over pairs of candidate bases.
No sorting, completeness or optimality of the table is trusted: the returned
rows still have to pass the exact membership and support checks for the actual
axis. Even arbitrary breakpoints or a default result cannot weaken the theorem.
-/

namespace N12Compact.SupportFan

open IntegerSupport PairPruning

structure Basis (r : Nat) where
  first : Fin r
  second : Fin r
  deriving DecidableEq

structure Entry (r : Nat) where
  start : Nat
  basis : Basis r
  deriving DecidableEq

def search {r : Nat} (entries : Array (Entry r)) (key : Nat) :
    Nat → Nat → Nat → Basis r → Basis r
  | 0, _, _, best => best
  | fuel + 1, lo, hi, best =>
      if lo < hi then
        let mid := (lo + hi) / 2
        match entries[mid]? with
        | none => best
        | some entry =>
            if entry.start ≤ key then
              search entries key fuel (mid + 1) hi entry.basis
            else search entries key fuel lo mid best
      else best

/-- Sixteen comparisons are enough for all pilot fans. Soundness does not
depend on that bound: the selected basis is always checked afterwards. -/
def select {r : Nat} (entries : Array (Entry r)) (key : Nat)
    (fallback : Basis r) : Basis r :=
  search entries key 16 0 entries.size fallback

def witness {r : Nat} (source neighbor : Array (Entry r))
    (keys : Fin 8 → Nat) (opposite : Nat → Nat) (fallback : Basis r)
    (i : Fin 8) : Support r :=
  let a := select source (keys i) fallback
  let b := select neighbor (opposite (keys i)) fallback
  ⟨a.first, a.second, b.first, b.second⟩

def AxisCheck {r : Nat} (rows : Fin r → Row)
    (aInputs bInputs : List (Fin r)) (a b : ReferenceAxis.Reference)
    (i : Fin 8) (w : Support r) : Prop :=
  w.a₁ ∈ aInputs ∧ w.a₂ ∈ aInputs ∧ w.b₁ ∈ bInputs ∧ w.b₂ ∈ bInputs ∧
  PairSupport.FastCheck (rows w.a₁) (rows w.a₂) (rows w.b₁) (rows w.b₂)
    (ReferenceAxis.target a b (direction a b i))

instance {r : Nat} (rows : Fin r → Row) (aInputs bInputs : List (Fin r))
    (a b : ReferenceAxis.Reference) (i : Fin 8) (w : Support r) :
    Decidable (AxisCheck rows aInputs bInputs a b i w) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem AxisCheck.toCheck {r : Nat} {rows : Fin r → Row}
    {aInputs bInputs : List (Fin r)} {a b : ReferenceAxis.Reference}
    {i : Fin 8} {w : Support r}
    (h : AxisCheck rows aInputs bInputs a b i w) :
    w.Check rows aInputs bInputs a b i :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.toCheck⟩

#print axioms AxisCheck.toCheck

end N12Compact.SupportFan
