import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data04
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2165, 2164)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2166, 2164)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2168, 2167)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2169, 2167)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2171, 2170)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2172, 2170)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2174, 2173)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2175, 2173)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2177, 2176)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2178, 2176)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2179, 2176)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2181, 2180)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2182, 2180)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2184, 2183)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2185, 2183)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2186, 2183)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2188, 2187)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2189, 2187)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2191, 2190)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2192, 2190)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2194, 2193)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2195, 2193)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2197, 2196)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2198, 2196)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2200, 2199)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2201, 2199)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2203, 2202)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2204, 2202)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2206, 2205)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2207, 2205)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2209, 2208)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2210, 2208)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2212, 2211)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2213, 2211)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2215, 2214)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2216, 2214)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2218, 2217)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2219, 2217)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2221, 2220)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2222, 2220)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2224, 2223)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2225, 2223)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2227, 2226)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2228, 2226)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2230, 2229)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2231, 2229)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2233, 2232)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2234, 2232)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2236, 2235)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2237, 2235)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2239, 2238)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2241, 2240)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2243, 2242)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2245, 2244)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2247, 2246)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2249, 2248)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2251, 2250)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2253, 2252)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2255, 2254)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2257, 2256)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2259, 2258)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2261, 2260)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2263, 2262)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2265, 2264)

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
end N12Compact.C898CompactRelaxation.Data04
