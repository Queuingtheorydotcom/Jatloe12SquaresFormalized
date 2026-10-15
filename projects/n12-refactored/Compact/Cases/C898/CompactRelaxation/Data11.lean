import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data11
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2908, 2906)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2909, 2906)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2911, 2910)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2912, 2910)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2913, 2910)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2914, 2910)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2915, 2910)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2916, 2910)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2917, 2910)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2919, 2918)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2920, 2918)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2921, 2918)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2922, 2918)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2923, 2918)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2924, 2918)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2926, 2925)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2927, 2925)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2928, 2925)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2929, 2925)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2930, 2925)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2931, 2925)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2933, 2932)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2934, 2932)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2935, 2932)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2936, 2932)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2937, 2932)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2938, 2932)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2939, 2932)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2940, 2932)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2941, 2932)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2943, 2942)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2944, 2942)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2945, 2942)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2946, 2942)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2947, 2942)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2948, 2942)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2949, 2942)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2950, 2942)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2951, 2942)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2953, 2952)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2955, 2954)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2957, 2956)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2959, 2958)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2961, 2960)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2963, 2962)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2965, 2964)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2967, 2966)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2969, 2968)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2971, 2970)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2973, 2972)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2975, 2974)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2977, 2976)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2979, 2978)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2981, 2980)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2983, 2982)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2985, 2984)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2987, 2986)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2989, 2988)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2991, 2990)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2993, 2992)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2995, 2994)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2997, 2996)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2999, 2998)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 3001, 3000)

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
end N12Compact.C898CompactRelaxation.Data11
