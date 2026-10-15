import Compact.Cases.C898.CachedPairs.CommonRaw03
import Compact.Cases.C898.CachedPairs.CommonRaw04
import Compact.Cases.C898.CachedPairs.CommonRaw05
import Compact.Cases.C898.CachedPairs.Step02Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step2CommonRawSources : Fin 47 → RawSupportFan.Context :=
  ![commonRaw237, commonRaw297, commonRaw298, commonRaw299, commonRaw300, commonRaw301, commonRaw302, commonRaw303, commonRaw304, commonRaw305, commonRaw306, commonRaw307, commonRaw308, commonRaw309, commonRaw310, commonRaw311, commonRaw312, commonRaw313, commonRaw314, commonRaw315, commonRaw316, commonRaw317, commonRaw318, commonRaw319, commonRaw320, commonRaw321, commonRaw322, commonRaw323, commonRaw324, commonRaw325, commonRaw326, commonRaw327, commonRaw328, commonRaw329, commonRaw330, commonRaw331, commonRaw332, commonRaw333, commonRaw334, commonRaw335, commonRaw336, commonRaw337, commonRaw338, commonRaw339, commonRaw340, commonRaw341, commonRaw342]
theorem step2CommonRawSources_exact (i : Fin 47) :
    step2CommonRawSources i = (step2Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw237_exact
  · exact commonRaw297_exact
  · exact commonRaw298_exact
  · exact commonRaw299_exact
  · exact commonRaw300_exact
  · exact commonRaw301_exact
  · exact commonRaw302_exact
  · exact commonRaw303_exact
  · exact commonRaw304_exact
  · exact commonRaw305_exact
  · exact commonRaw306_exact
  · exact commonRaw307_exact
  · exact commonRaw308_exact
  · exact commonRaw309_exact
  · exact commonRaw310_exact
  · exact commonRaw311_exact
  · exact commonRaw312_exact
  · exact commonRaw313_exact
  · exact commonRaw314_exact
  · exact commonRaw315_exact
  · exact commonRaw316_exact
  · exact commonRaw317_exact
  · exact commonRaw318_exact
  · exact commonRaw319_exact
  · exact commonRaw320_exact
  · exact commonRaw321_exact
  · exact commonRaw322_exact
  · exact commonRaw323_exact
  · exact commonRaw324_exact
  · exact commonRaw325_exact
  · exact commonRaw326_exact
  · exact commonRaw327_exact
  · exact commonRaw328_exact
  · exact commonRaw329_exact
  · exact commonRaw330_exact
  · exact commonRaw331_exact
  · exact commonRaw332_exact
  · exact commonRaw333_exact
  · exact commonRaw334_exact
  · exact commonRaw335_exact
  · exact commonRaw336_exact
  · exact commonRaw337_exact
  · exact commonRaw338_exact
  · exact commonRaw339_exact
  · exact commonRaw340_exact
  · exact commonRaw341_exact
  · exact commonRaw342_exact

def step2CommonSourceAngles : Fin 47 → Fin 64 :=
  ![6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem step2CommonSourceAngles_exact (i : Fin 47) :
    step2CommonSourceAngles i = (step2Sources i).keyAngle := by
  fin_cases i <;> rfl

def step2CommonRawNeighbors : Fin 59 → RawSupportFan.Context :=
  ![commonRaw238, commonRaw239, commonRaw240, commonRaw241, commonRaw242, commonRaw243, commonRaw244, commonRaw245, commonRaw246, commonRaw247, commonRaw248, commonRaw249, commonRaw250, commonRaw251, commonRaw252, commonRaw253, commonRaw254, commonRaw255, commonRaw256, commonRaw257, commonRaw258, commonRaw259, commonRaw260, commonRaw261, commonRaw262, commonRaw263, commonRaw264, commonRaw265, commonRaw266, commonRaw267, commonRaw268, commonRaw269, commonRaw270, commonRaw271, commonRaw272, commonRaw273, commonRaw274, commonRaw275, commonRaw276, commonRaw277, commonRaw278, commonRaw279, commonRaw280, commonRaw281, commonRaw282, commonRaw283, commonRaw284, commonRaw285, commonRaw286, commonRaw287, commonRaw288, commonRaw289, commonRaw290, commonRaw291, commonRaw292, commonRaw293, commonRaw294, commonRaw295, commonRaw296]
theorem step2CommonRawNeighbors_exact (i : Fin 59) :
    step2CommonRawNeighbors i = (step2Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw238_exact
  · exact commonRaw239_exact
  · exact commonRaw240_exact
  · exact commonRaw241_exact
  · exact commonRaw242_exact
  · exact commonRaw243_exact
  · exact commonRaw244_exact
  · exact commonRaw245_exact
  · exact commonRaw246_exact
  · exact commonRaw247_exact
  · exact commonRaw248_exact
  · exact commonRaw249_exact
  · exact commonRaw250_exact
  · exact commonRaw251_exact
  · exact commonRaw252_exact
  · exact commonRaw253_exact
  · exact commonRaw254_exact
  · exact commonRaw255_exact
  · exact commonRaw256_exact
  · exact commonRaw257_exact
  · exact commonRaw258_exact
  · exact commonRaw259_exact
  · exact commonRaw260_exact
  · exact commonRaw261_exact
  · exact commonRaw262_exact
  · exact commonRaw263_exact
  · exact commonRaw264_exact
  · exact commonRaw265_exact
  · exact commonRaw266_exact
  · exact commonRaw267_exact
  · exact commonRaw268_exact
  · exact commonRaw269_exact
  · exact commonRaw270_exact
  · exact commonRaw271_exact
  · exact commonRaw272_exact
  · exact commonRaw273_exact
  · exact commonRaw274_exact
  · exact commonRaw275_exact
  · exact commonRaw276_exact
  · exact commonRaw277_exact
  · exact commonRaw278_exact
  · exact commonRaw279_exact
  · exact commonRaw280_exact
  · exact commonRaw281_exact
  · exact commonRaw282_exact
  · exact commonRaw283_exact
  · exact commonRaw284_exact
  · exact commonRaw285_exact
  · exact commonRaw286_exact
  · exact commonRaw287_exact
  · exact commonRaw288_exact
  · exact commonRaw289_exact
  · exact commonRaw290_exact
  · exact commonRaw291_exact
  · exact commonRaw292_exact
  · exact commonRaw293_exact
  · exact commonRaw294_exact
  · exact commonRaw295_exact
  · exact commonRaw296_exact

def step2CommonNeighborAngles : Fin 59 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step2CommonNeighborAngles_exact (i : Fin 59) :
    step2CommonNeighborAngles i = (step2Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step2CommonNeighborUnblocked : ∀ j, (step2Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
