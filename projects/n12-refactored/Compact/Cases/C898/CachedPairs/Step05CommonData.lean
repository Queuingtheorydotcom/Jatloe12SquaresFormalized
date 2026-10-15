import Compact.Cases.C898.CachedPairs.CommonRaw06
import Compact.Cases.C898.CachedPairs.CommonRaw07
import Compact.Cases.C898.CachedPairs.Step05Data
import Compact.Cases.C898.CommonPairGroups
import Compact.Core.KernelMatrix

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared S12 CommonGroups
noncomputable section

def step5CommonRawSources : Fin 51 → RawSupportFan.Context :=
  ![commonRaw421, commonRaw434, commonRaw435, commonRaw436, commonRaw437, commonRaw438, commonRaw439, commonRaw440, commonRaw441, commonRaw442, commonRaw443, commonRaw444, commonRaw445, commonRaw446, commonRaw447, commonRaw448, commonRaw449, commonRaw450, commonRaw451, commonRaw452, commonRaw453, commonRaw454, commonRaw455, commonRaw456, commonRaw457, commonRaw458, commonRaw459, commonRaw460, commonRaw461, commonRaw462, commonRaw463, commonRaw464, commonRaw465, commonRaw466, commonRaw467, commonRaw468, commonRaw469, commonRaw470, commonRaw471, commonRaw472, commonRaw473, commonRaw474, commonRaw475, commonRaw476, commonRaw477, commonRaw478, commonRaw479, commonRaw480, commonRaw481, commonRaw482, commonRaw483]
theorem step5CommonRawSources_exact (i : Fin 51) :
    step5CommonRawSources i = (step5Sources i).context.numeric := by
  fin_cases i
  · exact commonRaw421_exact
  · exact commonRaw434_exact
  · exact commonRaw435_exact
  · exact commonRaw436_exact
  · exact commonRaw437_exact
  · exact commonRaw438_exact
  · exact commonRaw439_exact
  · exact commonRaw440_exact
  · exact commonRaw441_exact
  · exact commonRaw442_exact
  · exact commonRaw443_exact
  · exact commonRaw444_exact
  · exact commonRaw445_exact
  · exact commonRaw446_exact
  · exact commonRaw447_exact
  · exact commonRaw448_exact
  · exact commonRaw449_exact
  · exact commonRaw450_exact
  · exact commonRaw451_exact
  · exact commonRaw452_exact
  · exact commonRaw453_exact
  · exact commonRaw454_exact
  · exact commonRaw455_exact
  · exact commonRaw456_exact
  · exact commonRaw457_exact
  · exact commonRaw458_exact
  · exact commonRaw459_exact
  · exact commonRaw460_exact
  · exact commonRaw461_exact
  · exact commonRaw462_exact
  · exact commonRaw463_exact
  · exact commonRaw464_exact
  · exact commonRaw465_exact
  · exact commonRaw466_exact
  · exact commonRaw467_exact
  · exact commonRaw468_exact
  · exact commonRaw469_exact
  · exact commonRaw470_exact
  · exact commonRaw471_exact
  · exact commonRaw472_exact
  · exact commonRaw473_exact
  · exact commonRaw474_exact
  · exact commonRaw475_exact
  · exact commonRaw476_exact
  · exact commonRaw477_exact
  · exact commonRaw478_exact
  · exact commonRaw479_exact
  · exact commonRaw480_exact
  · exact commonRaw481_exact
  · exact commonRaw482_exact
  · exact commonRaw483_exact

def step5CommonSourceAngles : Fin 51 → Fin 64 :=
  ![12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62]
theorem step5CommonSourceAngles_exact (i : Fin 51) :
    step5CommonSourceAngles i = (step5Sources i).keyAngle := by
  fin_cases i <;> rfl

def step5CommonRawNeighbors : Fin 12 → RawSupportFan.Context :=
  ![commonRaw422, commonRaw423, commonRaw424, commonRaw425, commonRaw426, commonRaw427, commonRaw428, commonRaw429, commonRaw430, commonRaw431, commonRaw432, commonRaw433]
theorem step5CommonRawNeighbors_exact (i : Fin 12) :
    step5CommonRawNeighbors i = (step5Neighbors i).context.numeric := by
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

def step5CommonNeighborAngles : Fin 12 → Fin 64 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 63]
theorem step5CommonNeighborAngles_exact (i : Fin 12) :
    step5CommonNeighborAngles i = (step5Neighbors i).keyAngle := by
  fin_cases i <;> rfl

theorem step5CommonNeighborUnblocked : ∀ j, (step5Neighbors j).block = [] := by
  intro j; fin_cases j <;> rfl


end
end N12Compact.C898Cached.AllPairs
