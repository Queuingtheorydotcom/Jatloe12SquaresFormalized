import Compact.Cases.C898.CachedPairs.CommonRaw14
import Compact.Cases.C898.CachedPairs.CommonRaw15
import Compact.Cases.C898.CachedPairs.Step13Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step13CommonRawSources : Fin 23 → RawSupportFan.Context :=
  ![commonRaw916, commonRaw980, commonRaw981, commonRaw982, commonRaw983, commonRaw984, commonRaw985, commonRaw986, commonRaw987, commonRaw988, commonRaw989, commonRaw990, commonRaw991, commonRaw992, commonRaw993, commonRaw994, commonRaw995, commonRaw996, commonRaw997, commonRaw998, commonRaw999, commonRaw1000, commonRaw1001]
theorem step13CommonRawSources_exact (i : Fin 23) :
    step13CommonRawSources i = (step13Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw916_exact
  · exact commonRaw980_exact
  · exact commonRaw981_exact
  · exact commonRaw982_exact
  · exact commonRaw983_exact
  · exact commonRaw984_exact
  · exact commonRaw985_exact
  · exact commonRaw986_exact
  · exact commonRaw987_exact
  · exact commonRaw988_exact
  · exact commonRaw989_exact
  · exact commonRaw990_exact
  · exact commonRaw991_exact
  · exact commonRaw992_exact
  · exact commonRaw993_exact
  · exact commonRaw994_exact
  · exact commonRaw995_exact
  · exact commonRaw996_exact
  · exact commonRaw997_exact
  · exact commonRaw998_exact
  · exact commonRaw999_exact
  · exact commonRaw1000_exact
  · exact commonRaw1001_exact

def step13CommonSourceAngles : Fin 23 → Fin 64 :=
  ![11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]
theorem step13CommonSourceAngles_exact (i : Fin 23) :
    step13CommonSourceAngles i = (step13Sources i).keyAngle := by
  fin_cases i <;> rfl

def step13CommonRawNeighbors : Fin 63 → RawSupportFan.Context :=
  ![commonRaw917, commonRaw918, commonRaw919, commonRaw920, commonRaw921, commonRaw922, commonRaw923, commonRaw924, commonRaw925, commonRaw926, commonRaw927, commonRaw928, commonRaw929, commonRaw930, commonRaw931, commonRaw932, commonRaw933, commonRaw934, commonRaw935, commonRaw936, commonRaw937, commonRaw938, commonRaw939, commonRaw940, commonRaw941, commonRaw942, commonRaw943, commonRaw944, commonRaw945, commonRaw946, commonRaw947, commonRaw948, commonRaw949, commonRaw950, commonRaw951, commonRaw952, commonRaw953, commonRaw954, commonRaw955, commonRaw956, commonRaw957, commonRaw958, commonRaw959, commonRaw960, commonRaw961, commonRaw962, commonRaw963, commonRaw964, commonRaw965, commonRaw966, commonRaw967, commonRaw968, commonRaw969, commonRaw970, commonRaw971, commonRaw972, commonRaw973, commonRaw974, commonRaw975, commonRaw976, commonRaw977, commonRaw978, commonRaw979]
theorem step13CommonRawNeighbors_exact (i : Fin 63) :
    step13CommonRawNeighbors i = (step13Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw917_exact
  · exact commonRaw918_exact
  · exact commonRaw919_exact
  · exact commonRaw920_exact
  · exact commonRaw921_exact
  · exact commonRaw922_exact
  · exact commonRaw923_exact
  · exact commonRaw924_exact
  · exact commonRaw925_exact
  · exact commonRaw926_exact
  · exact commonRaw927_exact
  · exact commonRaw928_exact
  · exact commonRaw929_exact
  · exact commonRaw930_exact
  · exact commonRaw931_exact
  · exact commonRaw932_exact
  · exact commonRaw933_exact
  · exact commonRaw934_exact
  · exact commonRaw935_exact
  · exact commonRaw936_exact
  · exact commonRaw937_exact
  · exact commonRaw938_exact
  · exact commonRaw939_exact
  · exact commonRaw940_exact
  · exact commonRaw941_exact
  · exact commonRaw942_exact
  · exact commonRaw943_exact
  · exact commonRaw944_exact
  · exact commonRaw945_exact
  · exact commonRaw946_exact
  · exact commonRaw947_exact
  · exact commonRaw948_exact
  · exact commonRaw949_exact
  · exact commonRaw950_exact
  · exact commonRaw951_exact
  · exact commonRaw952_exact
  · exact commonRaw953_exact
  · exact commonRaw954_exact
  · exact commonRaw955_exact
  · exact commonRaw956_exact
  · exact commonRaw957_exact
  · exact commonRaw958_exact
  · exact commonRaw959_exact
  · exact commonRaw960_exact
  · exact commonRaw961_exact
  · exact commonRaw962_exact
  · exact commonRaw963_exact
  · exact commonRaw964_exact
  · exact commonRaw965_exact
  · exact commonRaw966_exact
  · exact commonRaw967_exact
  · exact commonRaw968_exact
  · exact commonRaw969_exact
  · exact commonRaw970_exact
  · exact commonRaw971_exact
  · exact commonRaw972_exact
  · exact commonRaw973_exact
  · exact commonRaw974_exact
  · exact commonRaw975_exact
  · exact commonRaw976_exact
  · exact commonRaw977_exact
  · exact commonRaw978_exact
  · exact commonRaw979_exact

def step13CommonNeighborAngles : Fin 63 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step13CommonNeighborAngles_exact (i : Fin 63) :
    step13CommonNeighborAngles i = (step13Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step13CommonNeighborUnblocked : ∀ j, (step13Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
