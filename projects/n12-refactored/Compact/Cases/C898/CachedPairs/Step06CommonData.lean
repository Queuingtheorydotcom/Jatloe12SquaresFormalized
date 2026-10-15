import Compact.Cases.C898.CachedPairs.CommonRaw03
import Compact.Cases.C898.CachedPairs.CommonRaw04
import Compact.Cases.C898.CachedPairs.CommonRaw07
import Compact.Cases.C898.CachedPairs.CommonRaw08
import Compact.Cases.C898.CachedPairs.Step06Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step6CommonRawSources : Fin 59 → RawSupportFan.Context :=
  ![commonRaw484, commonRaw485, commonRaw486, commonRaw487, commonRaw488, commonRaw489, commonRaw490, commonRaw491, commonRaw492, commonRaw493, commonRaw494, commonRaw495, commonRaw496, commonRaw497, commonRaw498, commonRaw499, commonRaw500, commonRaw501, commonRaw502, commonRaw503, commonRaw504, commonRaw505, commonRaw506, commonRaw507, commonRaw508, commonRaw509, commonRaw510, commonRaw511, commonRaw512, commonRaw513, commonRaw514, commonRaw515, commonRaw516, commonRaw517, commonRaw518, commonRaw519, commonRaw520, commonRaw521, commonRaw522, commonRaw523, commonRaw524, commonRaw525, commonRaw526, commonRaw527, commonRaw528, commonRaw529, commonRaw530, commonRaw531, commonRaw532, commonRaw533, commonRaw534, commonRaw535, commonRaw536, commonRaw537, commonRaw538, commonRaw539, commonRaw540, commonRaw541, commonRaw542]
theorem step6CommonRawSources_exact (i : Fin 59) :
    step6CommonRawSources i = (step6Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw484_exact
  · exact commonRaw485_exact
  · exact commonRaw486_exact
  · exact commonRaw487_exact
  · exact commonRaw488_exact
  · exact commonRaw489_exact
  · exact commonRaw490_exact
  · exact commonRaw491_exact
  · exact commonRaw492_exact
  · exact commonRaw493_exact
  · exact commonRaw494_exact
  · exact commonRaw495_exact
  · exact commonRaw496_exact
  · exact commonRaw497_exact
  · exact commonRaw498_exact
  · exact commonRaw499_exact
  · exact commonRaw500_exact
  · exact commonRaw501_exact
  · exact commonRaw502_exact
  · exact commonRaw503_exact
  · exact commonRaw504_exact
  · exact commonRaw505_exact
  · exact commonRaw506_exact
  · exact commonRaw507_exact
  · exact commonRaw508_exact
  · exact commonRaw509_exact
  · exact commonRaw510_exact
  · exact commonRaw511_exact
  · exact commonRaw512_exact
  · exact commonRaw513_exact
  · exact commonRaw514_exact
  · exact commonRaw515_exact
  · exact commonRaw516_exact
  · exact commonRaw517_exact
  · exact commonRaw518_exact
  · exact commonRaw519_exact
  · exact commonRaw520_exact
  · exact commonRaw521_exact
  · exact commonRaw522_exact
  · exact commonRaw523_exact
  · exact commonRaw524_exact
  · exact commonRaw525_exact
  · exact commonRaw526_exact
  · exact commonRaw527_exact
  · exact commonRaw528_exact
  · exact commonRaw529_exact
  · exact commonRaw530_exact
  · exact commonRaw531_exact
  · exact commonRaw532_exact
  · exact commonRaw533_exact
  · exact commonRaw534_exact
  · exact commonRaw535_exact
  · exact commonRaw536_exact
  · exact commonRaw537_exact
  · exact commonRaw538_exact
  · exact commonRaw539_exact
  · exact commonRaw540_exact
  · exact commonRaw541_exact
  · exact commonRaw542_exact

def step6CommonSourceAngles : Fin 59 → Fin 64 :=
  ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]
theorem step6CommonSourceAngles_exact (i : Fin 59) :
    step6CommonSourceAngles i = (step6Sources i).keyAngle := by
  fin_cases i <;> rfl

def step6CommonRawNeighbors : Fin 59 → RawSupportFan.Context :=
  ![commonRaw238, commonRaw239, commonRaw240, commonRaw241, commonRaw242, commonRaw243, commonRaw244, commonRaw245, commonRaw246, commonRaw247, commonRaw248, commonRaw249, commonRaw250, commonRaw251, commonRaw252, commonRaw253, commonRaw254, commonRaw255, commonRaw256, commonRaw257, commonRaw258, commonRaw259, commonRaw260, commonRaw261, commonRaw262, commonRaw263, commonRaw264, commonRaw265, commonRaw266, commonRaw267, commonRaw268, commonRaw269, commonRaw270, commonRaw271, commonRaw272, commonRaw273, commonRaw274, commonRaw275, commonRaw276, commonRaw277, commonRaw278, commonRaw279, commonRaw280, commonRaw281, commonRaw282, commonRaw283, commonRaw284, commonRaw285, commonRaw286, commonRaw287, commonRaw288, commonRaw289, commonRaw290, commonRaw291, commonRaw292, commonRaw293, commonRaw294, commonRaw295, commonRaw296]
theorem step6CommonRawNeighbors_exact (i : Fin 59) :
    step6CommonRawNeighbors i = (step6Neighbors i).context.numeric := by
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

def step6CommonNeighborAngles : Fin 59 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step6CommonNeighborAngles_exact (i : Fin 59) :
    step6CommonNeighborAngles i = (step6Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step6CommonNeighborUnblocked : ∀ j, (step6Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
