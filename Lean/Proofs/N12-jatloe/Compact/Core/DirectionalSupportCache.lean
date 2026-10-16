import Compact.Core.RawSupportFanBool

/-! Reuse an exact support bound across every pair involving a context/key.

The datum contains only a direction, denominator, lower-row constant and
strictness bit. Its check certifies the selected basis cone and exact values
once. Later pair arithmetic contains no row lookups, Cramer calculations,
vertex dot products or proof-bearing contexts. Missing table entries reject
the pair. The generic bridge recovers the unchanged eight-axis predicate.
-/

set_option Elab.async false

namespace N12Compact.DirectionalSupportCache
open IntegerSupport ReferenceAxis PairPruning RawSupportFan

structure Datum where
  x : Int
  y : Int
  denominator : Int
  constant : Int
  strict : Bool
  deriving DecidableEq

def Datum.ofBasis (basis : VertexSupport.Basis) (x y : Int) : Datum :=
  ⟨x, y, basis.denominator, (basis.bound x y).constant, (basis.bound x y).strict⟩

def Datum.Check (datum : Datum) (context : Context) (key : Nat) : Prop :=
  let basis := (context.select key).basis
  basis.Cone datum.x datum.y ∧
    datum.denominator = basis.denominator ∧
    datum.constant = (basis.bound datum.x datum.y).constant ∧
    datum.strict = (basis.bound datum.x datum.y).strict

instance (datum : Datum) (context : Context) (key : Nat) :
    Decidable (datum.Check context key) :=
  inferInstanceAs (Decidable (_ ∧ _))

def pair (a b : Datum) (x y scale constant : Int) : Bool :=
  let lhs := scale * (b.denominator * a.constant + a.denominator * b.constant)
  let rhs := a.denominator * b.denominator * constant
  decide (a.x = x) && (decide (a.y = y) &&
  (decide (b.x = -x) && (decide (b.y = -y) &&
  (decide (lhs ≤ rhs) && (decide (lhs < rhs) || (a.strict || b.strict))))))

theorem pair_sound (a b : Datum) (A B : Context) (ka kb : Nat)
    (ha : a.Check A ka) (hb : b.Check B kb) (x y scale constant : Int)
    (checked : pair a b x y scale constant = true) :
    (A.select ka).basis.Cone x y ∧ (B.select kb).basis.Cone (-x) (-y) ∧
      VertexSupport.PairCheck (A.select ka).basis (B.select kb).basis
        x y scale constant := by
  simp only [pair, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at checked
  obtain ⟨ax, ay, bx, by_, numeric⟩ := checked
  change (A.select ka).basis.Cone a.x a.y ∧ _ at ha
  change (B.select kb).basis.Cone b.x b.y ∧ _ at hb
  rw [ax, ay] at ha
  rw [bx, by_] at hb
  refine ⟨ha.1, hb.1, ?_⟩
  simpa only [VertexSupport.PairCheck, ha.2.1, hb.2.1,
    ha.2.2.1, hb.2.2.1, ha.2.2.2, hb.2.2.2] using numeric

/-- A producer may use a balanced sparse lookup over only requested keys.
The numeric type contains no global dictionary or semantic proof. -/
structure Table where
  reference : Reference
  lookup : Nat → Option Datum

def Table.Check (table : Table) (context : Context) : Prop :=
  table.reference = context.reference ∧
    ∀ (key : Nat) (datum : Datum), table.lookup key = some datum → datum.Check context key

def axis (a b : Table) (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (i : Fin 8) : Bool :=
  match a.lookup (keys i), b.lookup (opposite (keys i)) with
  | some A, some B =>
      let n := direction a.reference b.reference i
      pair A B n.x n.y (CachedSupportFan.scale a.reference b.reference)
        (target a.reference b.reference n).constant
  | _, _ => false

def all8 (f : Fin 8 → Bool) : Bool :=
  f 0 && (f 1 && (f 2 && (f 3 && (f 4 && (f 5 && (f 6 && f 7))))))

theorem all8_sound (f : Fin 8 → Bool) (checked : all8 f = true) (i : Fin 8) :
    f i = true := by
  simp only [all8, Bool.and_eq_true] at checked
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
      i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked.1
  · exact checked.2.1
  · exact checked.2.2.1
  · exact checked.2.2.2.1
  · exact checked.2.2.2.2.1
  · exact checked.2.2.2.2.2.1
  · exact checked.2.2.2.2.2.2.1
  · exact checked.2.2.2.2.2.2.2

def check (a b : Table) (keys : Fin 8 → Nat) (opposite : Nat → Nat) : Bool :=
  all8 (axis a b keys opposite)

theorem check_sound (a b : Table) (A B : Context)
    (ha : a.Check A) (hb : b.Check B)
    (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : check a b keys opposite = true) : PairCheck A B keys opposite := by
  intro i
  have h := all8_sound (axis a b keys opposite) checked i
  cases ea : a.lookup (keys i) with
  | none => simp [axis, ea] at h
  | some da =>
      cases eb : b.lookup (opposite (keys i)) with
      | none => simp [axis, ea, eb] at h
      | some db =>
          have hp := pair_sound da db A B (keys i) (opposite (keys i))
            (ha.2 _ _ ea) (hb.2 _ _ eb)
            (direction a.reference b.reference i).x
            (direction a.reference b.reference i).y
            (CachedSupportFan.scale a.reference b.reference)
            (target a.reference b.reference (direction a.reference b.reference i)).constant
            (by simpa only [axis, ea, eb] using h)
          simpa only [ha.1, hb.1] using hp

end N12Compact.DirectionalSupportCache

#print axioms N12Compact.DirectionalSupportCache.check_sound
