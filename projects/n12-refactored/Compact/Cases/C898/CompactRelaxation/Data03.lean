import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data03
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 2062, 2060)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 2064, 2063)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 2065, 2063)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 2067, 2066)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 2069, 2068)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 2071, 2070)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 2073, 2072)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 2075, 2074)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 2077, 2076)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 2079, 2078)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 2081, 2080)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 2083, 2082)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 2085, 2084)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 2087, 2086)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 2089, 2088)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 2091, 2090)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 2093, 2092)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 2095, 2094)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 2097, 2096)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 2098, 2096)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 2100, 2099)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 2101, 2099)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 2102, 2099)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2103, 2099)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2105, 2104)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2106, 2104)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2107, 2104)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2108, 2104)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2109, 2104)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2111, 2110)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2112, 2110)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2113, 2110)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2114, 2110)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2115, 2110)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2117, 2116)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2118, 2116)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2119, 2116)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2120, 2116)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2122, 2121)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2124, 2123)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2126, 2125)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2128, 2127)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2130, 2129)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2132, 2131)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2134, 2133)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2136, 2135)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2137, 2135)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2138, 2135)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2140, 2139)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2141, 2139)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2143, 2142)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2144, 2142)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2146, 2145)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2147, 2145)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2149, 2148)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2151, 2150)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2152, 2150)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2154, 2153)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2155, 2153)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2157, 2156)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2159, 2158)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2160, 2158)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2162, 2161)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2163, 2161)

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
end N12Compact.C898CompactRelaxation.Data03
