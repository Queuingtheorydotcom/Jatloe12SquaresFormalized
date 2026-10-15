import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data14
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 3256, 3255)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 3258, 3257)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 3260, 3259)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 3262, 3261)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 3264, 3263)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 3266, 3265)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 3268, 3267)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 3270, 3269)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 3272, 3271)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 3274, 3273)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 3276, 3275)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 3278, 3277)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 3280, 3279)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 3282, 3281)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 3284, 3283)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 3286, 3285)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 3288, 3287)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 3290, 3289)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 3292, 3291)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 3294, 3293)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 3296, 3295)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 3298, 3297)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 3300, 3299)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 3302, 3301)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 3304, 3303)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 3306, 3305)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 3308, 3307)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 3310, 3309)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 3312, 3311)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 3314, 3313)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 3316, 3315)

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
  entry30
]

def get (i : Fin 31) : Entry dictionary :=
  data[i.val]'(by change i.val < 31; exact i.isLt)

def Claim (i : Fin 31) : Prop := (get i).Check

instance (i : Fin 31) : Decidable (Claim i) :=
  inferInstanceAs (Decidable ((get i).Check))

theorem block0 : FiniteCheckChunks.Check Claim 0 := by
  decide +kernel

theorem block1 : FiniteCheckChunks.Check Claim 1 := by
  decide +kernel

theorem block2 : FiniteCheckChunks.Check Claim 2 := by
  decide +kernel

theorem block3 : FiniteCheckChunks.Check Claim 3 := by
  decide +kernel

theorem checked (i : Fin 31) : (get i).Check := by
  refine FiniteCheckChunks.sound Claim (count := 4) (by decide) ?_ i
  intro part
  fin_cases part
  · exact block0
  · exact block1
  · exact block2
  · exact block3

end
end N12Compact.C898CompactRelaxation.Data14
