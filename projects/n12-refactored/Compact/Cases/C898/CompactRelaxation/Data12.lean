import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data12
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 3003, 3002)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 3005, 3004)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 3007, 3006)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 3009, 3008)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 3011, 3010)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 3013, 3012)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 3015, 3014)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 3017, 3016)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 3019, 3018)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 3021, 3020)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 3023, 3022)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 3025, 3024)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 3027, 3026)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 3029, 3028)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 3031, 3030)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 3033, 3032)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 3035, 3034)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 3037, 3036)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 3039, 3038)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 3041, 3040)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 3043, 3042)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 3045, 3044)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 3047, 3046)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 3049, 3048)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 3051, 3050)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 3053, 3052)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 3055, 3054)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 3057, 3056)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 3059, 3058)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 3061, 3060)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 3063, 3062)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 3065, 3064)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 3067, 3066)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 3069, 3068)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 3071, 3070)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 3073, 3072)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 3075, 3074)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 3077, 3076)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 3079, 3078)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 3081, 3080)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 3083, 3082)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 3085, 3084)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 3087, 3086)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 3089, 3088)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 3091, 3090)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 3093, 3092)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 3095, 3094)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 3097, 3096)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 3099, 3098)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 3101, 3100)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 3103, 3102)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 3105, 3104)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 3107, 3106)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 3109, 3108)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 3111, 3110)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 3113, 3112)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 3115, 3114)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 3117, 3116)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 3119, 3118)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 3121, 3120)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 3123, 3122)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 3125, 3124)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 3127, 3126)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 3129, 3128)

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
end N12Compact.C898CompactRelaxation.Data12
