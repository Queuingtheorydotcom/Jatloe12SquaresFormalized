import Compact.Cases.C898.CachedPairs.CommonRaw10
import Compact.Cases.C898.CachedPairs.CommonRaw11
import Compact.Cases.C898.CachedPairs.CommonRaw12
import Compact.Cases.C898.CachedPairs.Step08Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step8CommonRawSources : Fin 64 → RawSupportFan.Context :=
  ![commonRaw656, commonRaw721, commonRaw722, commonRaw723, commonRaw724, commonRaw725, commonRaw726, commonRaw727, commonRaw728, commonRaw729, commonRaw730, commonRaw731, commonRaw732, commonRaw733, commonRaw734, commonRaw735, commonRaw736, commonRaw737, commonRaw738, commonRaw739, commonRaw740, commonRaw741, commonRaw742, commonRaw743, commonRaw744, commonRaw745, commonRaw746, commonRaw747, commonRaw748, commonRaw749, commonRaw750, commonRaw751, commonRaw752, commonRaw753, commonRaw754, commonRaw755, commonRaw756, commonRaw757, commonRaw758, commonRaw759, commonRaw760, commonRaw761, commonRaw762, commonRaw763, commonRaw764, commonRaw765, commonRaw766, commonRaw767, commonRaw768, commonRaw769, commonRaw770, commonRaw771, commonRaw772, commonRaw773, commonRaw774, commonRaw775, commonRaw776, commonRaw777, commonRaw778, commonRaw779, commonRaw780, commonRaw781, commonRaw782, commonRaw783]
theorem step8CommonRawSources_exact (i : Fin 64) :
    step8CommonRawSources i = (step8Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw656_exact
  · exact commonRaw721_exact
  · exact commonRaw722_exact
  · exact commonRaw723_exact
  · exact commonRaw724_exact
  · exact commonRaw725_exact
  · exact commonRaw726_exact
  · exact commonRaw727_exact
  · exact commonRaw728_exact
  · exact commonRaw729_exact
  · exact commonRaw730_exact
  · exact commonRaw731_exact
  · exact commonRaw732_exact
  · exact commonRaw733_exact
  · exact commonRaw734_exact
  · exact commonRaw735_exact
  · exact commonRaw736_exact
  · exact commonRaw737_exact
  · exact commonRaw738_exact
  · exact commonRaw739_exact
  · exact commonRaw740_exact
  · exact commonRaw741_exact
  · exact commonRaw742_exact
  · exact commonRaw743_exact
  · exact commonRaw744_exact
  · exact commonRaw745_exact
  · exact commonRaw746_exact
  · exact commonRaw747_exact
  · exact commonRaw748_exact
  · exact commonRaw749_exact
  · exact commonRaw750_exact
  · exact commonRaw751_exact
  · exact commonRaw752_exact
  · exact commonRaw753_exact
  · exact commonRaw754_exact
  · exact commonRaw755_exact
  · exact commonRaw756_exact
  · exact commonRaw757_exact
  · exact commonRaw758_exact
  · exact commonRaw759_exact
  · exact commonRaw760_exact
  · exact commonRaw761_exact
  · exact commonRaw762_exact
  · exact commonRaw763_exact
  · exact commonRaw764_exact
  · exact commonRaw765_exact
  · exact commonRaw766_exact
  · exact commonRaw767_exact
  · exact commonRaw768_exact
  · exact commonRaw769_exact
  · exact commonRaw770_exact
  · exact commonRaw771_exact
  · exact commonRaw772_exact
  · exact commonRaw773_exact
  · exact commonRaw774_exact
  · exact commonRaw775_exact
  · exact commonRaw776_exact
  · exact commonRaw777_exact
  · exact commonRaw778_exact
  · exact commonRaw779_exact
  · exact commonRaw780_exact
  · exact commonRaw781_exact
  · exact commonRaw782_exact
  · exact commonRaw783_exact

def step8CommonSourceAngles : Fin 64 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step8CommonSourceAngles_exact (i : Fin 64) :
    step8CommonSourceAngles i = (step8Sources i).keyAngle := by
  fin_cases i <;> rfl

def step8CommonRawNeighbors : Fin 64 → RawSupportFan.Context :=
  ![commonRaw657, commonRaw658, commonRaw659, commonRaw660, commonRaw661, commonRaw662, commonRaw663, commonRaw664, commonRaw665, commonRaw666, commonRaw667, commonRaw668, commonRaw669, commonRaw670, commonRaw671, commonRaw672, commonRaw673, commonRaw674, commonRaw675, commonRaw676, commonRaw677, commonRaw678, commonRaw679, commonRaw680, commonRaw681, commonRaw682, commonRaw683, commonRaw684, commonRaw685, commonRaw686, commonRaw687, commonRaw688, commonRaw689, commonRaw690, commonRaw691, commonRaw692, commonRaw693, commonRaw694, commonRaw695, commonRaw696, commonRaw697, commonRaw698, commonRaw699, commonRaw700, commonRaw701, commonRaw702, commonRaw703, commonRaw704, commonRaw705, commonRaw706, commonRaw707, commonRaw708, commonRaw709, commonRaw710, commonRaw711, commonRaw712, commonRaw713, commonRaw714, commonRaw715, commonRaw716, commonRaw717, commonRaw718, commonRaw719, commonRaw720]
theorem step8CommonRawNeighbors_exact (i : Fin 64) :
    step8CommonRawNeighbors i = (step8Neighbors i).context.numeric := by
  fin_cases i
  · exact commonRaw657_exact
  · exact commonRaw658_exact
  · exact commonRaw659_exact
  · exact commonRaw660_exact
  · exact commonRaw661_exact
  · exact commonRaw662_exact
  · exact commonRaw663_exact
  · exact commonRaw664_exact
  · exact commonRaw665_exact
  · exact commonRaw666_exact
  · exact commonRaw667_exact
  · exact commonRaw668_exact
  · exact commonRaw669_exact
  · exact commonRaw670_exact
  · exact commonRaw671_exact
  · exact commonRaw672_exact
  · exact commonRaw673_exact
  · exact commonRaw674_exact
  · exact commonRaw675_exact
  · exact commonRaw676_exact
  · exact commonRaw677_exact
  · exact commonRaw678_exact
  · exact commonRaw679_exact
  · exact commonRaw680_exact
  · exact commonRaw681_exact
  · exact commonRaw682_exact
  · exact commonRaw683_exact
  · exact commonRaw684_exact
  · exact commonRaw685_exact
  · exact commonRaw686_exact
  · exact commonRaw687_exact
  · exact commonRaw688_exact
  · exact commonRaw689_exact
  · exact commonRaw690_exact
  · exact commonRaw691_exact
  · exact commonRaw692_exact
  · exact commonRaw693_exact
  · exact commonRaw694_exact
  · exact commonRaw695_exact
  · exact commonRaw696_exact
  · exact commonRaw697_exact
  · exact commonRaw698_exact
  · exact commonRaw699_exact
  · exact commonRaw700_exact
  · exact commonRaw701_exact
  · exact commonRaw702_exact
  · exact commonRaw703_exact
  · exact commonRaw704_exact
  · exact commonRaw705_exact
  · exact commonRaw706_exact
  · exact commonRaw707_exact
  · exact commonRaw708_exact
  · exact commonRaw709_exact
  · exact commonRaw710_exact
  · exact commonRaw711_exact
  · exact commonRaw712_exact
  · exact commonRaw713_exact
  · exact commonRaw714_exact
  · exact commonRaw715_exact
  · exact commonRaw716_exact
  · exact commonRaw717_exact
  · exact commonRaw718_exact
  · exact commonRaw719_exact
  · exact commonRaw720_exact

def step8CommonNeighborAngles : Fin 64 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]
theorem step8CommonNeighborAngles_exact (i : Fin 64) :
    step8CommonNeighborAngles i = (step8Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step8CommonNeighborUnblocked : ∀ j, (step8Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
