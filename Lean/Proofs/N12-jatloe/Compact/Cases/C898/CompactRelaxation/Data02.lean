import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data02
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 1962, 1961)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 1964, 1963)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 1966, 1965)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 1968, 1967)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 1970, 1969)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 1972, 1971)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 1974, 1973)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 1976, 1975)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 1978, 1977)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 1980, 1979)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 1981, 1979)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 1983, 1982)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 1984, 1982)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 1986, 1985)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 1987, 1985)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 1989, 1988)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 1990, 1988)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 1992, 1991)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 1993, 1991)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 1995, 1994)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 1996, 1994)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 1998, 1997)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 1999, 1997)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 2001, 2000)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 2002, 2000)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 2004, 2003)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 2005, 2003)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 2007, 2006)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 2008, 2006)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 2010, 2009)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 2011, 2009)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 2013, 2012)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 2014, 2012)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 2016, 2015)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 2017, 2015)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 2019, 2018)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 2020, 2018)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 2022, 2021)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 2023, 2021)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 2025, 2024)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 2026, 2024)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 2028, 2027)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 2029, 2027)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 2031, 2030)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 2032, 2030)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 2034, 2033)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 2035, 2033)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 2037, 2036)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 2038, 2036)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 2040, 2039)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 2041, 2039)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 2043, 2042)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 2044, 2042)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 2046, 2045)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 2047, 2045)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 2049, 2048)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 2050, 2048)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 2052, 2051)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 2053, 2051)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 2055, 2054)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 2056, 2054)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 2058, 2057)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 2059, 2057)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 2061, 2060)

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
end N12Compact.C898CompactRelaxation.Data02
