import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data05
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2267, 2266)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2269, 2268)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2271, 2270)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2273, 2272)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2275, 2274)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2277, 2276)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2279, 2278)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2281, 2280)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2283, 2282)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2285, 2284)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2286, 2284)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2288, 2287)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2290, 2289)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2292, 2291)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2294, 2293)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2296, 2295)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2298, 2297)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2300, 2299)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2302, 2301)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2304, 2303)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2306, 2305)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2308, 2307)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2310, 2309)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2312, 2311)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2314, 2313)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2316, 2315)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2318, 2317)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2320, 2319)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2322, 2321)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2324, 2323)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2326, 2325)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2328, 2327)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2330, 2329)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2332, 2331)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2334, 2333)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2336, 2335)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2338, 2337)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2340, 2339)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2342, 2341)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2344, 2343)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2346, 2345)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2348, 2347)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2350, 2349)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2352, 2351)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2354, 2353)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2356, 2355)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2358, 2357)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2360, 2359)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2362, 2361)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2364, 2363)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2366, 2365)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2367, 2365)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2369, 2368)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2370, 2368)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2372, 2371)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2373, 2371)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2375, 2374)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2377, 2376)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2379, 2378)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2381, 2380)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2383, 2382)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2385, 2384)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2387, 2386)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2389, 2388)

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
end N12Compact.C898CompactRelaxation.Data05
