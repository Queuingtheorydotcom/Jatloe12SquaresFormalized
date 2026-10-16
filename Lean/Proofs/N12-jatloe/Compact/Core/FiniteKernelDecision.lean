import Compact.Core.FiniteCheckChunks
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Split a bounded finite check before kernel reduction. Every valid offset
is checked; impossible offsets in the final partial block are discharged from
their contradictory bound. This macro only assembles ordinary proof tactics.
-/

macro "split_kernel_check" : tactic =>
  `(tactic| (intro offset valid
             dsimp only
             fin_cases offset
             all_goals try norm_num at valid
             all_goals try clear valid
             all_goals decide +kernel))
