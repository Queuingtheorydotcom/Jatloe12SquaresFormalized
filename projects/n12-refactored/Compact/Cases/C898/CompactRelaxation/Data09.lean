import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data09
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2702, 2701)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2704, 2703)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2706, 2705)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2707, 2705)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2709, 2708)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2710, 2708)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2712, 2711)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2713, 2711)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2715, 2714)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2716, 2714)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2718, 2717)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2719, 2717)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2721, 2720)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2722, 2720)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2724, 2723)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2725, 2723)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2727, 2726)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2728, 2726)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2730, 2729)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2731, 2729)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2733, 2732)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2734, 2732)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2736, 2735)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2737, 2735)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2739, 2738)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2740, 2738)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2742, 2741)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2743, 2741)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2745, 2744)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2746, 2744)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2748, 2747)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2749, 2747)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2751, 2750)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2753, 2752)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2755, 2754)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2757, 2756)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2759, 2758)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2761, 2760)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2763, 2762)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2764, 2762)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2765, 2762)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2766, 2762)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2767, 2762)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2768, 2762)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2769, 2762)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2770, 2762)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2771, 2762)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2772, 2762)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2774, 2773)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2775, 2773)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2776, 2773)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2777, 2773)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2778, 2773)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2779, 2773)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2780, 2773)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2781, 2773)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2782, 2773)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2784, 2783)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2785, 2783)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2786, 2783)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2787, 2783)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2788, 2783)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2789, 2783)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2790, 2783)

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
end N12Compact.C898CompactRelaxation.Data09
