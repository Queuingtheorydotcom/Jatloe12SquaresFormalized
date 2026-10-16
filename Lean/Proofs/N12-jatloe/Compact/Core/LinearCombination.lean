import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Sparse linear contradictions and propagation-cycle closure

These generic lemmas are independent of the packing model. A packing adapter
must prove the inequalities supplied to them from the original geometry. A
certificate stores only nonzero weights and their source-row indices. It need
not store every intermediate enclosure from a numerical propagation trace.

The exact weighted sum or polynomial identity is a separate proof obligation.
In particular, a floating-point solver's answer is not an instance of any
theorem here. This module introduces no numerical decision oracle.
-/

namespace N12Compact

open scoped BigOperators

section LinearCombination

variable {K : Type u} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K] {Index : Type v}

/-- Soundness of a sparse nonnegative linear combination. Rows outside `support`
have no proof obligation and do not appear in the certificate. -/
theorem sparseCombination_nonneg (support : Finset Index)
    (weight row : Index → K)
    (weight_nonneg : ∀ i ∈ support, 0 ≤ weight i)
    (row_nonneg : ∀ i ∈ support, 0 ≤ row i) :
    0 ≤ ∑ i ∈ support, weight i * row i := by
  exact Finset.sum_nonneg fun i hi =>
    mul_nonneg (weight_nonneg i hi) (row_nonneg i hi)

/-- A negative exact combination refutes the conjunction of its source rows.
This is the Farkas-certificate form used by linear enclosure checkers. -/
theorem sparseCombination_refutes (support : Finset Index)
    (weight row : Index → K)
    (weight_nonneg : ∀ i ∈ support, 0 ≤ weight i)
    (row_nonneg : ∀ i ∈ support, 0 ≤ row i)
    (negative : (∑ i ∈ support, weight i * row i) < 0) : False :=
  (not_lt_of_ge (sparseCombination_nonneg support weight row
    weight_nonneg row_nonneg)) negative

/-- One strict source row with positive weight makes the entire combination
strict. Closed rows may still be used with arbitrary nonnegative weights. -/
theorem sparseCombination_pos (support : Finset Index)
    (weight row : Index → K)
    (weight_nonneg : ∀ i ∈ support, 0 ≤ weight i)
    (row_nonneg : ∀ i ∈ support, 0 ≤ row i)
    (strict : Index) (strict_mem : strict ∈ support)
    (strict_weight : 0 < weight strict) (strict_row : 0 < row strict) :
    0 < ∑ i ∈ support, weight i * row i := by
  have hterm : 0 < weight strict * row strict :=
    mul_pos strict_weight strict_row
  exact lt_of_lt_of_le hterm (Finset.single_le_sum
    (fun i hi => mul_nonneg (weight_nonneg i hi) (row_nonneg i hi)) strict_mem)

/-- Strict source inequalities can contradict an exactly zero combination.
This avoids artificially replacing strict packing inequalities by numerical
epsilon margins and preserves their boundary semantics. -/
theorem strictCombination_refutes (support : Finset Index)
    (weight row : Index → K)
    (weight_nonneg : ∀ i ∈ support, 0 ≤ weight i)
    (row_nonneg : ∀ i ∈ support, 0 ≤ row i)
    (strict : Index) (strict_mem : strict ∈ support)
    (strict_weight : 0 < weight strict) (strict_row : 0 < row strict)
    (nonpositive : (∑ i ∈ support, weight i * row i) ≤ 0) : False :=
  (not_lt_of_ge nonpositive) (sparseCombination_pos support weight row
    weight_nonneg row_nonneg strict strict_mem strict_weight strict_row)

/-- A symbolic exact identity is sufficient; repeated geometric inequalities
need not be re-expanded into every descendant certificate. -/
theorem constantCombination_refutes (support : Finset Index)
    (weight row : Index → K) (constant : K)
    (weight_nonneg : ∀ i ∈ support, 0 ≤ weight i)
    (row_nonneg : ∀ i ∈ support, 0 ≤ row i)
    (identity : (∑ i ∈ support, weight i * row i) = constant)
    (negative : constant < 0) : False := by
  apply sparseCombination_refutes support weight row weight_nonneg row_nonneg
  rw [identity]
  exact negative

end LinearCombination

section Contraction

variable {K : Type u} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Eliminate a self-dependent upper bound symbolically, before replaying any
iterations. No limiting argument or convergence computation is involved. -/
theorem contraction_bound (gain offset x : K)
    (bound : x ≤ gain * x + offset) : (1 - gain) * x ≤ offset := by
  have shifted : x - gain * x ≤ offset := by
    apply (sub_le_iff_le_add).2
    simpa only [add_comm] using bound
  calc
    (1 - gain) * x = x - gain * x := by ring
    _ ≤ offset := shifted

/-- A positive geometric deficit cannot satisfy a contractive homogeneous
cycle. Applications must prove the gain and the cycle inequality exactly. -/
theorem contraction_refutes (gain offset x : K)
    (gain_lt_one : gain < 1) (offset_nonpos : offset ≤ 0)
    (positive : 0 < x) (bound : x ≤ gain * x + offset) : False := by
  have strict : 0 < (1 - gain) * x :=
    mul_pos (sub_pos.mpr gain_lt_one) positive
  have nonpositive : (1 - gain) * x ≤ 0 :=
    le_trans (contraction_bound gain offset x bound) offset_nonpos
  exact (not_lt_of_ge nonpositive) strict

/-- Two coupled bounds close in one algebraic step instead of an arbitrarily
long alternating propagation chain. More general cycles can be collapsed into
the preceding scalar theorem or a sparse linear combination. -/
theorem twoNodeCycle_refutes (a b x y : K)
    (a_nonneg : 0 ≤ a) (gain_lt_one : a * b < 1) (positive : 0 < x)
    (forward : x ≤ a * y) (backward : y ≤ b * x) : False := by
  have cycle : x ≤ (a * b) * x + 0 := by
    calc
      x ≤ a * y := forward
      _ ≤ a * (b * x) := mul_le_mul_of_nonneg_left backward a_nonneg
      _ = (a * b) * x + 0 := by ring
  exact contraction_refutes (a * b) 0 x gain_lt_one (le_refl 0) positive cycle

end Contraction

end N12Compact
