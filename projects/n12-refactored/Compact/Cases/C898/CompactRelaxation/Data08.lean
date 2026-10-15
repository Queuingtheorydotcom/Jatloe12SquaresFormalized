import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data08
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2597, 2594)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2599, 2598)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2600, 2598)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2601, 2598)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2603, 2602)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2604, 2602)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2605, 2602)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2607, 2606)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2608, 2606)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2610, 2609)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2611, 2609)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2613, 2612)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2614, 2612)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2616, 2615)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2617, 2615)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2619, 2618)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2620, 2618)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2622, 2621)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2623, 2621)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2625, 2624)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2626, 2624)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2628, 2627)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2630, 2629)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2632, 2631)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2634, 2633)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2635, 2633)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2637, 2636)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2638, 2636)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2640, 2639)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2641, 2639)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2643, 2642)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2644, 2642)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2646, 2645)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2647, 2645)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2649, 2648)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2650, 2648)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2652, 2651)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2653, 2651)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2655, 2654)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2656, 2654)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2658, 2657)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2659, 2657)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2661, 2660)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2662, 2660)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2664, 2663)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2665, 2663)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2667, 2666)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2668, 2666)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2670, 2669)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2672, 2671)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2674, 2673)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2676, 2675)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2678, 2677)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2680, 2679)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2682, 2681)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2684, 2683)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2686, 2685)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2688, 2687)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2690, 2689)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2692, 2691)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2694, 2693)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2696, 2695)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2698, 2697)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2700, 2699)

def data : Array (Entry dictionary) := #[
  entry0,
  entry1,
  entry2,
  entry3,
  entry4,
  entry5,
  entry6,
  entry7,
  entry8,
  entry9,
  entry10,
  entry11,
  entry12,
  entry13,
  entry14,
  entry15,
  entry16,
  entry17,
  entry18,
  entry19,
  entry20,
  entry21,
  entry22,
  entry23,
  entry24,
  entry25,
  entry26,
  entry27,
  entry28,
  entry29,
  entry30,
  entry31,
  entry32,
  entry33,
  entry34,
  entry35,
  entry36,
  entry37,
  entry38,
  entry39,
  entry40,
  entry41,
  entry42,
  entry43,
  entry44,
  entry45,
  entry46,
  entry47,
  entry48,
  entry49,
  entry50,
  entry51,
  entry52,
  entry53,
  entry54,
  entry55,
  entry56,
  entry57,
  entry58,
  entry59,
  entry60,
  entry61,
  entry62,
  entry63
]

def get (i : Fin 64) : Entry dictionary :=
  data[i.val]'(by change i.val < 64; exact i.isLt)

def Claim (i : Fin 64) : Prop := (get i).Check

instance (i : Fin 64) : Decidable (Claim i) :=
  inferInstanceAs (Decidable ((get i).Check))

theorem block0 : FiniteCheckChunks.Check Claim 0 := by
  decide +kernel

theorem block1 : FiniteCheckChunks.Check Claim 1 := by
  decide +kernel

theorem block2 : FiniteCheckChunks.Check Claim 2 := by
  decide +kernel

theorem block3 : FiniteCheckChunks.Check Claim 3 := by
  decide +kernel

theorem block4 : FiniteCheckChunks.Check Claim 4 := by
  decide +kernel

theorem block5 : FiniteCheckChunks.Check Claim 5 := by
  decide +kernel

theorem block6 : FiniteCheckChunks.Check Claim 6 := by
  decide +kernel

theorem block7 : FiniteCheckChunks.Check Claim 7 := by
  decide +kernel

theorem checked (i : Fin 64) : (get i).Check := by
  refine FiniteCheckChunks.sound Claim (count := 8) (by decide) ?_ i
  intro part
  fin_cases part
  · exact block0
  · exact block1
  · exact block2
  · exact block3
  · exact block4
  · exact block5
  · exact block6
  · exact block7

end
end N12Compact.C898CompactRelaxation.Data08
