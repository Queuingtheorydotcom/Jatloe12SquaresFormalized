import Compact.Core.IntegerSupport

/-! Bounded acceptance batches limit each kernel decision's reduction cache.
This partitions a finite universal statement without adding mathematical
cases or discarding the final partial batch. No native decision is used.
-/

namespace N12Compact.FiniteCheckChunks

def Check {n : Nat} (claim : Fin n → Prop) (block : Nat) : Prop :=
  ∀ offset : Fin 8, ∀ h : block * 8 + offset.val < n,
    claim ⟨block * 8 + offset.val, h⟩

instance {n : Nat} (claim : Fin n → Prop) [DecidablePred claim] (block : Nat) :
    Decidable (Check claim block) :=
  inferInstanceAs (Decidable (∀ offset : Fin 8, ∀ h : _, _))

theorem sound {n count : Nat} (claim : Fin n → Prop) (covers : n ≤ count * 8)
    (checked : ∀ block : Fin count, Check claim block.val) (i : Fin n) : claim i := by
  let block : Fin count := ⟨i.val / 8, by omega⟩
  let offset : Fin 8 := ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩
  have exact_index : block.val * 8 + offset.val = i.val := by
    dsimp [block,offset]
    omega
  have valid : block.val * 8 + offset.val < n := by rw [exact_index]; exact i.isLt
  have h := checked block offset valid
  have same : (⟨block.val * 8 + offset.val,valid⟩ : Fin n) = i := Fin.ext exact_index
  simpa only [same] using h

#print axioms sound
end N12Compact.FiniteCheckChunks
