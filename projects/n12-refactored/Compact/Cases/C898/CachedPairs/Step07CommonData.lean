import Compact.Cases.C898.CachedPairs.CommonRaw08
import Compact.Cases.C898.CachedPairs.CommonRaw09
import Compact.Cases.C898.CachedPairs.CommonRaw10
import Compact.Cases.C898.CachedPairs.Step07Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step7CommonRawSources : Fin 49 → RawSupportFan.Context :=
  ![commonRaw543, commonRaw608, commonRaw609, commonRaw610, commonRaw611, commonRaw612, commonRaw613, commonRaw614, commonRaw615, commonRaw616, commonRaw617, commonRaw618, commonRaw619, commonRaw620, commonRaw621, commonRaw622, commonRaw623, commonRaw624, commonRaw625, commonRaw626, commonRaw627, commonRaw628, commonRaw629, commonRaw630, commonRaw631, commonRaw632, commonRaw633, commonRaw634, commonRaw635, commonRaw636, commonRaw637, commonRaw638, commonRaw639, commonRaw640, commonRaw641, commonRaw642, commonRaw643, commonRaw644, commonRaw645, commonRaw646, commonRaw647, commonRaw648, commonRaw649, commonRaw650, commonRaw651, commonRaw652, commonRaw653, commonRaw654, commonRaw655]
theorem step7CommonRawSources_exact (i : Fin 49) :
    step7CommonRawSources i = (step7Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw543_exact
  · exact commonRaw608_exact
  · exact commonRaw609_exact
  · exact commonRaw610_exact
  · exact commonRaw611_exact
  · exact commonRaw612_exact
  · exact commonRaw613_exact
  · exact commonRaw614_exact
  · exact commonRaw615_exact
  · exact commonRaw616_exact
  · exact commonRaw617_exact
  · exact commonRaw618_exact
  · exact commonRaw619_exact
  · exact commonRaw620_exact
  · exact commonRaw621_exact
  · exact commonRaw622_exact
  · exact commonRaw623_exact
  · exact commonRaw624_exact
  · exact commonRaw625_exact
  · exact commonRaw626_exact
  · exact commonRaw627_exact
  · exact commonRaw628_exact
  · exact commonRaw629_exact
  · exact commonRaw630_exact
  · exact commonRaw631_exact
  · exact commonRaw632_exact
  · exact commonRaw633_exact
  · exact commonRaw634_exact
  · exact commonRaw635_exact
  · exact commonRaw636_exact
  · exact commonRaw637_exact
  · exact commonRaw638_exact
  · exact commonRaw639_exact
  · exact commonRaw640_exact
  · exact commonRaw641_exact
  · exact commonRaw642_exact
  · exact commonRaw643_exact
  · exact commonRaw644_exact
  · exact commonRaw645_exact
  · exact commonRaw646_exact
  · exact commonRaw647_exact
  · exact commonRaw648_exact
  · exact commonRaw649_exact
  · exact commonRaw650_exact
  · exact commonRaw651_exact
  · exact commonRaw652_exact
  · exact commonRaw653_exact
  · exact commonRaw654_exact
  · exact commonRaw655_exact

def step7CommonSourceAngles : Fin 49 → Fin 64 :=
  ![2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57]
theorem step7CommonSourceAngles_exact (i : Fin 49) :
    step7CommonSourceAngles i = (step7Sources i).keyAngle := by
  fin_cases i <;> rfl

def step7CommonRawNeighbors : Fin 64 → RawSupportFan.Context :=
  ![commonRaw544, commonRaw545, commonRaw546, commonRaw547, commonRaw548, commonRaw549, commonRaw550, commonRaw551, commonRaw552, commonRaw553, commonRaw554, commonRaw555, commonRaw556, commonRaw557, commonRaw558, commonRaw559, commonRaw560, commonRaw561, commonRaw562, commonRaw563, commonRaw564, commonRaw565, commonRaw566, commonRaw567, commonRaw568, commonRaw569, commonRaw570, commonRaw571, commonRaw572, commonRaw573, commonRaw574, commonRaw575, commonRaw576, commonRaw577, commonRaw578, commonRaw579, commonRaw580, commonRaw581, commonRaw582, commonRaw583, commonRaw584, commonRaw585, commonRaw586, commonRaw587, commonRaw588, commonRaw589, commonRaw590, commonRaw591, commonRaw592, commonRaw593, commonRaw594, commonRaw595, commonRaw596, commonRaw597, commonRaw598, commonRaw599, commonRaw600, commonRaw601, commonRaw602, commonRaw603, commonRaw604, commonRaw605, commonRaw606, commonRaw607]
theorem step7CommonRawNeighbors_exact (i : Fin 64) :
    step7CommonRawNeighbors i = (step7Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw544_exact
  · exact commonRaw545_exact
  · exact commonRaw546_exact
  · exact commonRaw547_exact
  · exact commonRaw548_exact
  · exact commonRaw549_exact
  · exact commonRaw550_exact
  · exact commonRaw551_exact
  · exact commonRaw552_exact
  · exact commonRaw553_exact
  · exact commonRaw554_exact
  · exact commonRaw555_exact
  · exact commonRaw556_exact
  · exact commonRaw557_exact
  · exact commonRaw558_exact
  · exact commonRaw559_exact
  · exact commonRaw560_exact
  · exact commonRaw561_exact
  · exact commonRaw562_exact
  · exact commonRaw563_exact
  · exact commonRaw564_exact
  · exact commonRaw565_exact
  · exact commonRaw566_exact
  · exact commonRaw567_exact
  · exact commonRaw568_exact
  · exact commonRaw569_exact
  · exact commonRaw570_exact
  · exact commonRaw571_exact
  · exact commonRaw572_exact
  · exact commonRaw573_exact
  · exact commonRaw574_exact
  · exact commonRaw575_exact
  · exact commonRaw576_exact
  · exact commonRaw577_exact
  · exact commonRaw578_exact
  · exact commonRaw579_exact
  · exact commonRaw580_exact
  · exact commonRaw581_exact
  · exact commonRaw582_exact
  · exact commonRaw583_exact
  · exact commonRaw584_exact
  · exact commonRaw585_exact
  · exact commonRaw586_exact
  · exact commonRaw587_exact
  · exact commonRaw588_exact
  · exact commonRaw589_exact
  · exact commonRaw590_exact
  · exact commonRaw591_exact
  · exact commonRaw592_exact
  · exact commonRaw593_exact
  · exact commonRaw594_exact
  · exact commonRaw595_exact
  · exact commonRaw596_exact
  · exact commonRaw597_exact
  · exact commonRaw598_exact
  · exact commonRaw599_exact
  · exact commonRaw600_exact
  · exact commonRaw601_exact
  · exact commonRaw602_exact
  · exact commonRaw603_exact
  · exact commonRaw604_exact
  · exact commonRaw605_exact
  · exact commonRaw606_exact
  · exact commonRaw607_exact

def step7CommonNeighborAngles : Fin 64 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step7CommonNeighborAngles_exact (i : Fin 64) :
    step7CommonNeighborAngles i = (step7Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step7CommonNeighborUnblocked : ∀ j, (step7Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
