import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data07
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2494, 2493)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2495, 2493)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2497, 2496)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2498, 2496)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2500, 2499)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2501, 2499)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2503, 2502)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2504, 2502)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2506, 2505)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2507, 2505)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2509, 2508)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2510, 2508)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2511, 2508)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2513, 2512)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2515, 2514)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2517, 2516)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2519, 2518)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2521, 2520)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2523, 2522)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2525, 2524)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2527, 2526)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2529, 2528)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2531, 2530)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2533, 2532)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2535, 2534)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2537, 2536)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2539, 2538)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2541, 2540)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2543, 2542)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2545, 2544)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2547, 2546)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2549, 2548)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2551, 2550)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2552, 2550)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2554, 2553)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2555, 2553)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2557, 2556)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2558, 2556)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2560, 2559)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2561, 2559)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2563, 2562)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2564, 2562)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2566, 2565)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2567, 2565)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2569, 2568)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2570, 2568)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2572, 2571)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2573, 2571)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2575, 2574)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2576, 2574)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2578, 2577)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2579, 2577)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2581, 2580)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2582, 2580)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2584, 2583)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2585, 2583)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2587, 2586)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2588, 2586)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2589, 2586)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2591, 2590)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2592, 2590)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2593, 2590)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2595, 2594)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2596, 2594)

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
end N12Compact.C898CompactRelaxation.Data07
