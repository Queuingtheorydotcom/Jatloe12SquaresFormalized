import Compact.Core.IntegerSupport
import Lean.Elab.Command

/-! Exhaustive finite matrix checks with bounded kernel reduction.

The public theorem is proved by one generic range-composition argument. The
command supplies only opaque acceptance facts for at most eight consecutive
matrix entries and a balanced tree of applications of that argument. It does
not generate a case split, use native evaluation, or add trusted declarations.
Every numerical leaf is accepted by the ordinary `decide +kernel` tactic.
-/

namespace N12Compact.KernelMatrix

def Range (claim : Nat → Prop) (start count : Nat) : Prop :=
  ∀ i : Fin count, claim (start + i.val)

instance (claim : Nat → Prop) [DecidablePred claim] (start count : Nat) :
    Decidable (Range claim start count) :=
  inferInstanceAs (Decidable (∀ i : Fin count, _))

theorem Range.empty (claim : Nat → Prop) (start : Nat) : Range claim start 0 := by
  intro i
  exact Fin.elim0 i

theorem Range.append (claim : Nat → Prop) (start left right : Nat)
    (hl : Range claim start left) (hr : Range claim (start + left) right) :
    Range claim start (left + right) := by
  intro i
  by_cases h : i.val < left
  · exact hl ⟨i.val, h⟩
  · have hb : i.val - left < right := by omega
    have he : start + left + (i.val - left) = start + i.val := by omega
    simpa only [he] using hr ⟨i.val - left, hb⟩

/-- The guard handles empty matrix dimensions without partial indexing. -/
def Flat {m n : Nat} (claim : Fin m → Fin n → Prop) (index : Nat) : Prop :=
  ∀ hi : index / n < m, ∀ hj : index % n < n,
    claim ⟨index / n, hi⟩ ⟨index % n, hj⟩

instance {m n : Nat} (claim : Fin m → Fin n → Prop)
    [∀ i j, Decidable (claim i j)] (index : Nat) : Decidable (Flat claim index) :=
  inferInstanceAs (Decidable (∀ hi : _, ∀ hj : _, _))

theorem sound {m n : Nat} (claim : Fin m → Fin n → Prop)
    (checked : Range (Flat claim) 0 (m * n)) (i : Fin m) (j : Fin n) : claim i j := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  have hk : i.val * n + j.val < m * n := by
    calc
      i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
  have hi : (i.val * n + j.val) / n = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt j.isLt,
      Nat.zero_add]
  have hj : (i.val * n + j.val) % n = j.val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  have h := checked ⟨i.val * n + j.val, hk⟩
  simp only [Nat.zero_add, Flat] at h
  have a : (i.val * n + j.val) / n < m := by rw [hi]; exact i.isLt
  have b : (i.val * n + j.val) % n < n := by rw [hj]; exact j.isLt
  have first : (⟨(i.val * n + j.val) / n, a⟩ : Fin m) = i := Fin.ext hi
  have second : (⟨(i.val * n + j.val) % n, b⟩ : Fin n) = j := Fin.ext hj
  simpa only [first, second] using h a b

end N12Compact.KernelMatrix

namespace N12Compact.KernelMatrixSyntax
open Lean Elab Command

syntax (name := kernelMatrix) "kernel_matrix " ident " : " num " × " num
  " => " term : command

private def numeral (value : Nat) : TSyntax `term :=
  ⟨Syntax.mkNumLit (toString value)⟩

elab_rules : command
  | `(kernel_matrix $name:ident : $m:num × $n:num => $predicate:term) => do
      let total := m.getNat * n.getNat
      let claim := mkIdent (name.getId.appendAfter "_kernelPredicate")
      elabCommand (← `(private abbrev $claim : Fin $m → Fin $n → Prop := $predicate))
      let flat ← `(N12Compact.KernelMatrix.Flat $claim)
      let mut layer : Array (Nat × Nat × TSyntax `term) := #[]
      for block in [: (total + 7) / 8] do
        let start := block * 8
        let count := min 8 (total - start)
        let blockName := mkIdent (name.getId.appendAfter s!"_kernelBlock{block}")
        let startTerm := numeral start
        let countTerm := numeral count
        elabCommand (← `(private theorem $blockName :
          N12Compact.KernelMatrix.Range $flat $startTerm $countTerm := by decide +kernel))
        layer := layer.push (start, count, ← `($blockName:ident))
      if layer.isEmpty then
        layer := #[(0, 0, ← `(N12Compact.KernelMatrix.Range.empty $flat 0))]
      while layer.size > 1 do
        let mut next : Array (Nat × Nat × TSyntax `term) := #[]
        for pair in [: (layer.size + 1) / 2] do
          let left := layer[pair * 2]!
          if h : pair * 2 + 1 < layer.size then
            let right := layer[pair * 2 + 1]'h
            let start := numeral left.1
            let leftSize := numeral left.2.1
            let rightSize := numeral right.2.1
            let leftProof := left.2.2
            let rightProof := right.2.2
            let proof ← `(N12Compact.KernelMatrix.Range.append $flat $start
              $leftSize $rightSize $leftProof $rightProof)
            next := next.push (left.1, left.2.1 + right.2.1, proof)
          else
            next := next.push left
        layer := next
      let proof := layer[0]!.2.2
      elabCommand (← `(theorem $name (i : Fin $m) (j : Fin $n) : $predicate i j :=
        N12Compact.KernelMatrix.sound $claim $proof i j))

end N12Compact.KernelMatrixSyntax

namespace N12Compact.KernelMatrix

kernel_matrix example_checked : 2 × 5 => (fun i j => i.val + j.val < 7)
kernel_matrix empty_checked : 0 × 5 => (fun _ _ => False)

#print axioms sound
#print axioms example_checked
#print axioms empty_checked

end N12Compact.KernelMatrix
