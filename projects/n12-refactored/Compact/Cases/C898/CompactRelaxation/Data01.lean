import Compact.Core.RelaxationSyntax
import Compact.Core.FiniteCheckChunks
import Compact.Cases.C898.SharedDictionary
import Mathlib.Tactic.FinCases

/-! Original source/target pose IDs determine these relaxation records.
Local caches and support hints are independently checked by the kernel. -/
set_option Elab.async false
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898CompactRelaxation.Data01
open S12 S12Pilot C898Shared RelaxationTable
noncomputable section

def entry0 : Entry dictionary :=
  cached_relaxation%(dictionary, 1847, 1845)

def entry1 : Entry dictionary :=
  cached_relaxation%(dictionary, 1849, 1848)

def entry2 : Entry dictionary :=
  cached_relaxation%(dictionary, 1850, 1848)

def entry3 : Entry dictionary :=
  cached_relaxation%(dictionary, 1852, 1851)

def entry4 : Entry dictionary :=
  cached_relaxation%(dictionary, 1853, 1851)

def entry5 : Entry dictionary :=
  cached_relaxation%(dictionary, 1855, 1854)

def entry6 : Entry dictionary :=
  cached_relaxation%(dictionary, 1856, 1854)

def entry7 : Entry dictionary :=
  cached_relaxation%(dictionary, 1857, 1854)

def entry8 : Entry dictionary :=
  cached_relaxation%(dictionary, 1859, 1858)

def entry9 : Entry dictionary :=
  cached_relaxation%(dictionary, 1860, 1858)

def entry10 : Entry dictionary :=
  cached_relaxation%(dictionary, 1861, 1858)

def entry11 : Entry dictionary :=
  cached_relaxation%(dictionary, 1863, 1862)

def entry12 : Entry dictionary :=
  cached_relaxation%(dictionary, 1864, 1862)

def entry13 : Entry dictionary :=
  cached_relaxation%(dictionary, 1865, 1862)

def entry14 : Entry dictionary :=
  cached_relaxation%(dictionary, 1867, 1866)

def entry15 : Entry dictionary :=
  cached_relaxation%(dictionary, 1868, 1866)

def entry16 : Entry dictionary :=
  cached_relaxation%(dictionary, 1869, 1866)

def entry17 : Entry dictionary :=
  cached_relaxation%(dictionary, 1871, 1870)

def entry18 : Entry dictionary :=
  cached_relaxation%(dictionary, 1872, 1870)

def entry19 : Entry dictionary :=
  cached_relaxation%(dictionary, 1873, 1870)

def entry20 : Entry dictionary :=
  cached_relaxation%(dictionary, 1875, 1874)

def entry21 : Entry dictionary :=
  cached_relaxation%(dictionary, 1876, 1874)

def entry22 : Entry dictionary :=
  cached_relaxation%(dictionary, 1878, 1877)

def entry23 : Entry dictionary :=
  cached_relaxation%(dictionary, 1880, 1879)

def entry24 : Entry dictionary :=
  cached_relaxation%(dictionary, 1882, 1881)

def entry25 : Entry dictionary :=
  cached_relaxation%(dictionary, 1884, 1883)

def entry26 : Entry dictionary :=
  cached_relaxation%(dictionary, 1886, 1885)

def entry27 : Entry dictionary :=
  cached_relaxation%(dictionary, 1888, 1887)

def entry28 : Entry dictionary :=
  cached_relaxation%(dictionary, 1890, 1889)

def entry29 : Entry dictionary :=
  cached_relaxation%(dictionary, 1892, 1891)

def entry30 : Entry dictionary :=
  cached_relaxation%(dictionary, 1894, 1893)

def entry31 : Entry dictionary :=
  cached_relaxation%(dictionary, 1896, 1895)

def entry32 : Entry dictionary :=
  cached_relaxation%(dictionary, 1898, 1897)

def entry33 : Entry dictionary :=
  cached_relaxation%(dictionary, 1900, 1899)

def entry34 : Entry dictionary :=
  cached_relaxation%(dictionary, 1902, 1901)

def entry35 : Entry dictionary :=
  cached_relaxation%(dictionary, 1904, 1903)

def entry36 : Entry dictionary :=
  cached_relaxation%(dictionary, 1906, 1905)

def entry37 : Entry dictionary :=
  cached_relaxation%(dictionary, 1908, 1907)

def entry38 : Entry dictionary :=
  cached_relaxation%(dictionary, 1910, 1909)

def entry39 : Entry dictionary :=
  cached_relaxation%(dictionary, 1912, 1911)

def entry40 : Entry dictionary :=
  cached_relaxation%(dictionary, 1914, 1913)

def entry41 : Entry dictionary :=
  cached_relaxation%(dictionary, 1916, 1915)

def entry42 : Entry dictionary :=
  cached_relaxation%(dictionary, 1918, 1917)

def entry43 : Entry dictionary :=
  cached_relaxation%(dictionary, 1920, 1919)

def entry44 : Entry dictionary :=
  cached_relaxation%(dictionary, 1922, 1921)

def entry45 : Entry dictionary :=
  cached_relaxation%(dictionary, 1924, 1923)

def entry46 : Entry dictionary :=
  cached_relaxation%(dictionary, 1926, 1925)

def entry47 : Entry dictionary :=
  cached_relaxation%(dictionary, 1928, 1927)

def entry48 : Entry dictionary :=
  cached_relaxation%(dictionary, 1930, 1929)

def entry49 : Entry dictionary :=
  cached_relaxation%(dictionary, 1932, 1931)

def entry50 : Entry dictionary :=
  cached_relaxation%(dictionary, 1934, 1933)

def entry51 : Entry dictionary :=
  cached_relaxation%(dictionary, 1936, 1935)

def entry52 : Entry dictionary :=
  cached_relaxation%(dictionary, 1938, 1937)

def entry53 : Entry dictionary :=
  cached_relaxation%(dictionary, 1940, 1939)

def entry54 : Entry dictionary :=
  cached_relaxation%(dictionary, 1942, 1941)

def entry55 : Entry dictionary :=
  cached_relaxation%(dictionary, 1944, 1943)

def entry56 : Entry dictionary :=
  cached_relaxation%(dictionary, 1946, 1945)

def entry57 : Entry dictionary :=
  cached_relaxation%(dictionary, 1948, 1947)

def entry58 : Entry dictionary :=
  cached_relaxation%(dictionary, 1950, 1949)

def entry59 : Entry dictionary :=
  cached_relaxation%(dictionary, 1952, 1951)

def entry60 : Entry dictionary :=
  cached_relaxation%(dictionary, 1954, 1953)

def entry61 : Entry dictionary :=
  cached_relaxation%(dictionary, 1956, 1955)

def entry62 : Entry dictionary :=
  cached_relaxation%(dictionary, 1958, 1957)

def entry63 : Entry dictionary :=
  cached_relaxation%(dictionary, 1960, 1959)

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
end N12Compact.C898CompactRelaxation.Data01
