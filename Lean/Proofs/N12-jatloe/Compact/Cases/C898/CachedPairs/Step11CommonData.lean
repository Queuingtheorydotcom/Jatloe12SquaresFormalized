import Compact.Cases.C898.CachedPairs.CommonRaw12
import Compact.Cases.C898.CachedPairs.CommonRaw13
import Compact.Cases.C898.CachedPairs.Step11Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step11CommonRawSources : Fin 22 → RawSupportFan.Context :=
  ![commonRaw784, commonRaw846, commonRaw847, commonRaw848, commonRaw849, commonRaw850, commonRaw851, commonRaw852, commonRaw853, commonRaw854, commonRaw855, commonRaw856, commonRaw857, commonRaw858, commonRaw859, commonRaw860, commonRaw861, commonRaw862, commonRaw863, commonRaw864, commonRaw865, commonRaw866]
theorem step11CommonRawSources_exact (i : Fin 22) :
    step11CommonRawSources i = (step11Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw784_exact
  · exact commonRaw846_exact
  · exact commonRaw847_exact
  · exact commonRaw848_exact
  · exact commonRaw849_exact
  · exact commonRaw850_exact
  · exact commonRaw851_exact
  · exact commonRaw852_exact
  · exact commonRaw853_exact
  · exact commonRaw854_exact
  · exact commonRaw855_exact
  · exact commonRaw856_exact
  · exact commonRaw857_exact
  · exact commonRaw858_exact
  · exact commonRaw859_exact
  · exact commonRaw860_exact
  · exact commonRaw861_exact
  · exact commonRaw862_exact
  · exact commonRaw863_exact
  · exact commonRaw864_exact
  · exact commonRaw865_exact
  · exact commonRaw866_exact

def step11CommonSourceAngles : Fin 22 → Fin 64 :=
  ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
theorem step11CommonSourceAngles_exact (i : Fin 22) :
    step11CommonSourceAngles i = (step11Sources i).keyAngle := by
  fin_cases i <;> rfl

def step11CommonRawNeighbors : Fin 61 → RawSupportFan.Context :=
  ![commonRaw785, commonRaw786, commonRaw787, commonRaw788, commonRaw789, commonRaw790, commonRaw791, commonRaw792, commonRaw793, commonRaw794, commonRaw795, commonRaw796, commonRaw797, commonRaw798, commonRaw799, commonRaw800, commonRaw801, commonRaw802, commonRaw803, commonRaw804, commonRaw805, commonRaw806, commonRaw807, commonRaw808, commonRaw809, commonRaw810, commonRaw811, commonRaw812, commonRaw813, commonRaw814, commonRaw815, commonRaw816, commonRaw817, commonRaw818, commonRaw819, commonRaw820, commonRaw821, commonRaw822, commonRaw823, commonRaw824, commonRaw825, commonRaw826, commonRaw827, commonRaw828, commonRaw829, commonRaw830, commonRaw831, commonRaw832, commonRaw833, commonRaw834, commonRaw835, commonRaw836, commonRaw837, commonRaw838, commonRaw839, commonRaw840, commonRaw841, commonRaw842, commonRaw843, commonRaw844, commonRaw845]
theorem step11CommonRawNeighbors_exact (i : Fin 61) :
    step11CommonRawNeighbors i = (step11Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw785_exact
  · exact commonRaw786_exact
  · exact commonRaw787_exact
  · exact commonRaw788_exact
  · exact commonRaw789_exact
  · exact commonRaw790_exact
  · exact commonRaw791_exact
  · exact commonRaw792_exact
  · exact commonRaw793_exact
  · exact commonRaw794_exact
  · exact commonRaw795_exact
  · exact commonRaw796_exact
  · exact commonRaw797_exact
  · exact commonRaw798_exact
  · exact commonRaw799_exact
  · exact commonRaw800_exact
  · exact commonRaw801_exact
  · exact commonRaw802_exact
  · exact commonRaw803_exact
  · exact commonRaw804_exact
  · exact commonRaw805_exact
  · exact commonRaw806_exact
  · exact commonRaw807_exact
  · exact commonRaw808_exact
  · exact commonRaw809_exact
  · exact commonRaw810_exact
  · exact commonRaw811_exact
  · exact commonRaw812_exact
  · exact commonRaw813_exact
  · exact commonRaw814_exact
  · exact commonRaw815_exact
  · exact commonRaw816_exact
  · exact commonRaw817_exact
  · exact commonRaw818_exact
  · exact commonRaw819_exact
  · exact commonRaw820_exact
  · exact commonRaw821_exact
  · exact commonRaw822_exact
  · exact commonRaw823_exact
  · exact commonRaw824_exact
  · exact commonRaw825_exact
  · exact commonRaw826_exact
  · exact commonRaw827_exact
  · exact commonRaw828_exact
  · exact commonRaw829_exact
  · exact commonRaw830_exact
  · exact commonRaw831_exact
  · exact commonRaw832_exact
  · exact commonRaw833_exact
  · exact commonRaw834_exact
  · exact commonRaw835_exact
  · exact commonRaw836_exact
  · exact commonRaw837_exact
  · exact commonRaw838_exact
  · exact commonRaw839_exact
  · exact commonRaw840_exact
  · exact commonRaw841_exact
  · exact commonRaw842_exact
  · exact commonRaw843_exact
  · exact commonRaw844_exact
  · exact commonRaw845_exact

def step11CommonNeighborAngles : Fin 61 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step11CommonNeighborAngles_exact (i : Fin 61) :
    step11CommonNeighborAngles i = (step11Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step11CommonNeighborUnblocked : ∀ j, (step11Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
