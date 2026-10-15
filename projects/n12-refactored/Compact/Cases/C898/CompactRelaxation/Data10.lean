import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data10
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2792, 2791)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2793, 2791)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2794, 2791)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2795, 2791)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2796, 2791)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2797, 2791)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2798, 2791)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2800, 2799)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2801, 2799)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2802, 2799)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2803, 2799)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2805, 2804)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2806, 2804)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2807, 2804)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2809, 2808)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2811, 2810)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2813, 2812)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2815, 2814)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2817, 2816)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2819, 2818)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2821, 2820)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2823, 2822)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2825, 2824)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2827, 2826)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2829, 2828)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2831, 2830)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2833, 2832)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2835, 2834)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2837, 2836)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2839, 2838)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2841, 2840)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2843, 2842)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2845, 2844)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2847, 2846)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2849, 2848)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2851, 2850)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2853, 2852)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2855, 2854)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2857, 2856)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2859, 2858)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2861, 2860)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2863, 2862)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2865, 2864)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2867, 2866)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2869, 2868)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2871, 2870)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2873, 2872)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2875, 2874)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2877, 2876)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2879, 2878)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2881, 2880)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2883, 2882)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2885, 2884)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2887, 2886)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2889, 2888)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2891, 2890)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2893, 2892)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2895, 2894)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2897, 2896)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2899, 2898)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2901, 2900)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2903, 2902)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2905, 2904)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2907, 2906)

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
end N12Compact.C898CompactRelaxation.Data10
