import Compact.Cases.C898.CachedPairs.CommonRaw06
import Compact.Cases.C898.CachedPairs.CommonRaw13
import Compact.Cases.C898.CachedPairs.CommonRaw14
import Compact.Cases.C898.CachedPairs.Step12Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step12CommonRawSources : Fin 49 → RawSupportFan.Context :=
  ![commonRaw867, commonRaw868, commonRaw869, commonRaw870, commonRaw871, commonRaw872, commonRaw873, commonRaw874, commonRaw875, commonRaw876, commonRaw877, commonRaw878, commonRaw879, commonRaw880, commonRaw881, commonRaw882, commonRaw883, commonRaw884, commonRaw885, commonRaw886, commonRaw887, commonRaw888, commonRaw889, commonRaw890, commonRaw891, commonRaw892, commonRaw893, commonRaw894, commonRaw895, commonRaw896, commonRaw897, commonRaw898, commonRaw899, commonRaw900, commonRaw901, commonRaw902, commonRaw903, commonRaw904, commonRaw905, commonRaw906, commonRaw907, commonRaw908, commonRaw909, commonRaw910, commonRaw911, commonRaw912, commonRaw913, commonRaw914, commonRaw915]
theorem step12CommonRawSources_exact (i : Fin 49) :
    step12CommonRawSources i = (step12Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw867_exact
  · exact commonRaw868_exact
  · exact commonRaw869_exact
  · exact commonRaw870_exact
  · exact commonRaw871_exact
  · exact commonRaw872_exact
  · exact commonRaw873_exact
  · exact commonRaw874_exact
  · exact commonRaw875_exact
  · exact commonRaw876_exact
  · exact commonRaw877_exact
  · exact commonRaw878_exact
  · exact commonRaw879_exact
  · exact commonRaw880_exact
  · exact commonRaw881_exact
  · exact commonRaw882_exact
  · exact commonRaw883_exact
  · exact commonRaw884_exact
  · exact commonRaw885_exact
  · exact commonRaw886_exact
  · exact commonRaw887_exact
  · exact commonRaw888_exact
  · exact commonRaw889_exact
  · exact commonRaw890_exact
  · exact commonRaw891_exact
  · exact commonRaw892_exact
  · exact commonRaw893_exact
  · exact commonRaw894_exact
  · exact commonRaw895_exact
  · exact commonRaw896_exact
  · exact commonRaw897_exact
  · exact commonRaw898_exact
  · exact commonRaw899_exact
  · exact commonRaw900_exact
  · exact commonRaw901_exact
  · exact commonRaw902_exact
  · exact commonRaw903_exact
  · exact commonRaw904_exact
  · exact commonRaw905_exact
  · exact commonRaw906_exact
  · exact commonRaw907_exact
  · exact commonRaw908_exact
  · exact commonRaw909_exact
  · exact commonRaw910_exact
  · exact commonRaw911_exact
  · exact commonRaw912_exact
  · exact commonRaw913_exact
  · exact commonRaw914_exact
  · exact commonRaw915_exact

def step12CommonSourceAngles : Fin 49 → Fin 64 :=
  ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50]
theorem step12CommonSourceAngles_exact (i : Fin 49) :
    step12CommonSourceAngles i = (step12Sources i).keyAngle := by
  fin_cases i <;> rfl

def step12CommonRawNeighbors : Fin 12 → RawSupportFan.Context :=
  ![commonRaw422, commonRaw423, commonRaw424, commonRaw425, commonRaw426, commonRaw427, commonRaw428, commonRaw429, commonRaw430, commonRaw431, commonRaw432, commonRaw433]
theorem step12CommonRawNeighbors_exact (i : Fin 12) :
    step12CommonRawNeighbors i = (step12Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw422_exact
  · exact commonRaw423_exact
  · exact commonRaw424_exact
  · exact commonRaw425_exact
  · exact commonRaw426_exact
  · exact commonRaw427_exact
  · exact commonRaw428_exact
  · exact commonRaw429_exact
  · exact commonRaw430_exact
  · exact commonRaw431_exact
  · exact commonRaw432_exact
  · exact commonRaw433_exact

def step12CommonNeighborAngles : Fin 12 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 63]
theorem step12CommonNeighborAngles_exact (i : Fin 12) :
    step12CommonNeighborAngles i = (step12Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step12CommonNeighborUnblocked : ∀ j, (step12Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
