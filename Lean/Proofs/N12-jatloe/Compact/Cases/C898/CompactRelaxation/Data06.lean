import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data06
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2391, 2390)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2393, 2392)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2395, 2394)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2397, 2396)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2399, 2398)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2400, 2398)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2402, 2401)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2403, 2401)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2405, 2404)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2406, 2404)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2408, 2407)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2409, 2407)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2411, 2410)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2412, 2410)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2414, 2413)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2415, 2413)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2417, 2416)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2418, 2416)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2420, 2419)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2421, 2419)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2423, 2422)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2424, 2422)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2426, 2425)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2427, 2425)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2429, 2428)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2430, 2428)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2432, 2431)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2433, 2431)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2435, 2434)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2436, 2434)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2438, 2437)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2439, 2437)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2441, 2440)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2443, 2442)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2445, 2444)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2447, 2446)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2449, 2448)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2451, 2450)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2453, 2452)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2455, 2454)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2457, 2456)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2459, 2458)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2461, 2460)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2462, 2460)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2464, 2463)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2465, 2463)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2467, 2466)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2468, 2466)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2470, 2469)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2471, 2469)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2473, 2472)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2474, 2472)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2476, 2475)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2477, 2475)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2479, 2478)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2480, 2478)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2482, 2481)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2483, 2481)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2485, 2484)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2486, 2484)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2488, 2487)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2489, 2487)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2491, 2490)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2492, 2490)

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
end N12Compact.C898CompactRelaxation.Data06
