import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data13
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 3131, 3130)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 3133, 3132)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 3135, 3134)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 3137, 3136)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 3139, 3138)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 3141, 3140)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 3143, 3142)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 3145, 3144)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 3147, 3146)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 3149, 3148)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 3151, 3150)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 3153, 3152)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 3155, 3154)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 3156, 3154)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 3158, 3157)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 3159, 3157)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 3161, 3160)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 3163, 3162)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 3165, 3164)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 3167, 3166)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 3168, 3166)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 3170, 3169)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 3172, 3171)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 3174, 3173)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 3176, 3175)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 3178, 3177)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 3180, 3179)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 3182, 3181)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 3184, 3183)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 3186, 3185)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 3188, 3187)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 3190, 3189)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 3192, 3191)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 3194, 3193)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 3196, 3195)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 3198, 3197)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 3200, 3199)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 3202, 3201)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 3204, 3203)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 3206, 3205)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 3208, 3207)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 3210, 3209)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 3212, 3211)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 3214, 3213)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 3216, 3215)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 3218, 3217)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 3220, 3219)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 3222, 3221)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 3224, 3223)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 3226, 3225)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 3228, 3227)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 3230, 3229)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 3232, 3231)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 3234, 3233)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 3236, 3235)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 3238, 3237)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 3240, 3239)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 3242, 3241)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 3244, 3243)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 3246, 3245)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 3248, 3247)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 3250, 3249)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 3252, 3251)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 3254, 3253)

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
end N12Compact.C898CompactRelaxation.Data13
