import Compact.Cases.C898.CachedPairs.CommonRaw00
import Compact.Cases.C898.CachedPairs.CommonRaw01
import Compact.Cases.C898.CachedPairs.Step00Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step0CommonRawSources : Fin 50 → RawSupportFan.Context :=
  ![commonRaw0, commonRaw60, commonRaw61, commonRaw62, commonRaw63, commonRaw64, commonRaw65, commonRaw66, commonRaw67, commonRaw68, commonRaw69, commonRaw70, commonRaw71, commonRaw72, commonRaw73, commonRaw74, commonRaw75, commonRaw76, commonRaw77, commonRaw78, commonRaw79, commonRaw80, commonRaw81, commonRaw82, commonRaw83, commonRaw84, commonRaw85, commonRaw86, commonRaw87, commonRaw88, commonRaw89, commonRaw90, commonRaw91, commonRaw92, commonRaw93, commonRaw94, commonRaw95, commonRaw96, commonRaw97, commonRaw98, commonRaw99, commonRaw100, commonRaw101, commonRaw102, commonRaw103, commonRaw104, commonRaw105, commonRaw106, commonRaw107, commonRaw108]
theorem step0CommonRawSources_exact (i : Fin 50) :
    step0CommonRawSources i = (step0Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw0_exact
  · exact commonRaw60_exact
  · exact commonRaw61_exact
  · exact commonRaw62_exact
  · exact commonRaw63_exact
  · exact commonRaw64_exact
  · exact commonRaw65_exact
  · exact commonRaw66_exact
  · exact commonRaw67_exact
  · exact commonRaw68_exact
  · exact commonRaw69_exact
  · exact commonRaw70_exact
  · exact commonRaw71_exact
  · exact commonRaw72_exact
  · exact commonRaw73_exact
  · exact commonRaw74_exact
  · exact commonRaw75_exact
  · exact commonRaw76_exact
  · exact commonRaw77_exact
  · exact commonRaw78_exact
  · exact commonRaw79_exact
  · exact commonRaw80_exact
  · exact commonRaw81_exact
  · exact commonRaw82_exact
  · exact commonRaw83_exact
  · exact commonRaw84_exact
  · exact commonRaw85_exact
  · exact commonRaw86_exact
  · exact commonRaw87_exact
  · exact commonRaw88_exact
  · exact commonRaw89_exact
  · exact commonRaw90_exact
  · exact commonRaw91_exact
  · exact commonRaw92_exact
  · exact commonRaw93_exact
  · exact commonRaw94_exact
  · exact commonRaw95_exact
  · exact commonRaw96_exact
  · exact commonRaw97_exact
  · exact commonRaw98_exact
  · exact commonRaw99_exact
  · exact commonRaw100_exact
  · exact commonRaw101_exact
  · exact commonRaw102_exact
  · exact commonRaw103_exact
  · exact commonRaw104_exact
  · exact commonRaw105_exact
  · exact commonRaw106_exact
  · exact commonRaw107_exact
  · exact commonRaw108_exact

def step0CommonSourceAngles : Fin 50 → Fin 64 :=
  ![6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]
theorem step0CommonSourceAngles_exact (i : Fin 50) :
    step0CommonSourceAngles i = (step0Sources i).keyAngle := by
  fin_cases i <;> rfl

def step0CommonRawNeighbors : Fin 59 → RawSupportFan.Context :=
  ![commonRaw1, commonRaw2, commonRaw3, commonRaw4, commonRaw5, commonRaw6, commonRaw7, commonRaw8, commonRaw9, commonRaw10, commonRaw11, commonRaw12, commonRaw13, commonRaw14, commonRaw15, commonRaw16, commonRaw17, commonRaw18, commonRaw19, commonRaw20, commonRaw21, commonRaw22, commonRaw23, commonRaw24, commonRaw25, commonRaw26, commonRaw27, commonRaw28, commonRaw29, commonRaw30, commonRaw31, commonRaw32, commonRaw33, commonRaw34, commonRaw35, commonRaw36, commonRaw37, commonRaw38, commonRaw39, commonRaw40, commonRaw41, commonRaw42, commonRaw43, commonRaw44, commonRaw45, commonRaw46, commonRaw47, commonRaw48, commonRaw49, commonRaw50, commonRaw51, commonRaw52, commonRaw53, commonRaw54, commonRaw55, commonRaw56, commonRaw57, commonRaw58, commonRaw59]
theorem step0CommonRawNeighbors_exact (i : Fin 59) :
    step0CommonRawNeighbors i = (step0Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw1_exact
  · exact commonRaw2_exact
  · exact commonRaw3_exact
  · exact commonRaw4_exact
  · exact commonRaw5_exact
  · exact commonRaw6_exact
  · exact commonRaw7_exact
  · exact commonRaw8_exact
  · exact commonRaw9_exact
  · exact commonRaw10_exact
  · exact commonRaw11_exact
  · exact commonRaw12_exact
  · exact commonRaw13_exact
  · exact commonRaw14_exact
  · exact commonRaw15_exact
  · exact commonRaw16_exact
  · exact commonRaw17_exact
  · exact commonRaw18_exact
  · exact commonRaw19_exact
  · exact commonRaw20_exact
  · exact commonRaw21_exact
  · exact commonRaw22_exact
  · exact commonRaw23_exact
  · exact commonRaw24_exact
  · exact commonRaw25_exact
  · exact commonRaw26_exact
  · exact commonRaw27_exact
  · exact commonRaw28_exact
  · exact commonRaw29_exact
  · exact commonRaw30_exact
  · exact commonRaw31_exact
  · exact commonRaw32_exact
  · exact commonRaw33_exact
  · exact commonRaw34_exact
  · exact commonRaw35_exact
  · exact commonRaw36_exact
  · exact commonRaw37_exact
  · exact commonRaw38_exact
  · exact commonRaw39_exact
  · exact commonRaw40_exact
  · exact commonRaw41_exact
  · exact commonRaw42_exact
  · exact commonRaw43_exact
  · exact commonRaw44_exact
  · exact commonRaw45_exact
  · exact commonRaw46_exact
  · exact commonRaw47_exact
  · exact commonRaw48_exact
  · exact commonRaw49_exact
  · exact commonRaw50_exact
  · exact commonRaw51_exact
  · exact commonRaw52_exact
  · exact commonRaw53_exact
  · exact commonRaw54_exact
  · exact commonRaw55_exact
  · exact commonRaw56_exact
  · exact commonRaw57_exact
  · exact commonRaw58_exact
  · exact commonRaw59_exact

def step0CommonNeighborAngles : Fin 59 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step0CommonNeighborAngles_exact (i : Fin 59) :
    step0CommonNeighborAngles i = (step0Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step0CommonNeighborUnblocked : ∀ j, (step0Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
