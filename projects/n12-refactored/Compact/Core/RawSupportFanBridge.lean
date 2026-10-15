import Compact.Core.RawSupportFan

/-! Erasing semantic evidence preserves the exact fan lookup and checker.
This lets existing original-model adapters reuse their checked statements
while new numeric batches operate on small literal raw contexts.
-/

set_option Elab.async false

namespace N12Compact.CachedSupportFan
open IntegerSupport

theorem search_numeric {r : Nat} {rows : Fin r → Row} {inputs : List (Fin r)}
    (entries : Array (Certified rows inputs)) (key fuel lo hi : Nat)
    (best : Certified rows inputs) :
    RawSupportFan.search (entries.map (fun entry => entry.val.numeric)) key
      fuel lo hi best.val.numeric =
      (search entries key fuel lo hi best).val.numeric := by
  induction fuel generalizing lo hi best with
  | zero => rfl
  | succ fuel ih =>
      simp only [RawSupportFan.search, search]
      split
      · rw [Array.getElem?_map]
        cases hlookup : entries[(lo + hi) / 2]? with
        | none => simp [hlookup]
        | some entry =>
            simp only [hlookup, Option.map_some]
            dsimp only [Option.map, Entry.numeric]
            by_cases hle : entry.val.start ≤ key
            · simpa only [Option.map, Entry.numeric, hle, ↓reduceIte] using
                ih ((lo + hi) / 2 + 1) hi entry
            · simpa only [Option.map, Entry.numeric, hle, ↓reduceIte] using
                ih lo ((lo + hi) / 2) best
      · rfl

theorem Context.select_numeric {r : Nat} {rows : Fin r → Row}
    (context : Context rows) (key : Nat) :
    context.numeric.select key = (context.select key).val.numeric := by
  simpa only [Context.numeric, Context.select, RawSupportFan.Context.select,
    Array.size_map] using
      search_numeric context.entries key 16 0 context.entries.size context.fallback

theorem PairCheck.of_numeric {r : Nat} {rows : Fin r → Row}
    (a b : Context rows) (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : RawSupportFan.PairCheck a.numeric b.numeric keys opposite) :
    PairCheck a b keys opposite := by
  intro i
  have h := checked i
  rw [a.select_numeric, b.select_numeric] at h
  exact h

theorem PairCheck.of_cached_numeric {r : Nat} {rows : Fin r → Row}
    (a b : Context rows) (rawA rawB : RawSupportFan.Context)
    (a_exact : rawA = a.numeric) (b_exact : rawB = b.numeric)
    (keys : Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : RawSupportFan.PairCheck rawA rawB keys opposite) :
    PairCheck a b keys opposite := by
  subst rawA
  subst rawB
  exact PairCheck.of_numeric a b keys opposite checked

end N12Compact.CachedSupportFan

#print axioms N12Compact.CachedSupportFan.PairCheck.of_cached_numeric
