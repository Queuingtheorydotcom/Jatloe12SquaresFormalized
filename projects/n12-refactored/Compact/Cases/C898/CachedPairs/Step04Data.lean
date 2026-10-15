import Compact.Cases.C898.CachedPairs.Contexts01
import Compact.Cases.C898.CachedPairs.Contexts02
import Compact.Cases.C898.CachedPairs.Contexts06
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step4SourcesData : Array PoseContext := #[
  route414, route415, route416, route417, route418, route419, route420
]

def step4Sources (i : Fin 7) : PoseContext :=
  step4SourcesData[i.val]'(by change i.val < 7; exact i.isLt)

def step4NeighborsData : Array PoseContext := #[
  route110, route111, route112, route113, route114, route115, route116, route117, route118, route119, route120, route121, route122, route123, route124, route125, route126, route127, route128, route129, route130, route131, route132, route133, route134, route135, route136, route137, route138, route139, route140, route141, route142, route143, route144, route145, route146, route147, route148, route149, route150, route151, route152, route153, route154, route155, route156, route157, route158, route159, route160, route161, route162, route163, route164, route165, route166, route167, route168, route169, route170, route171, route172, route173
]

def step4Neighbors (i : Fin 64) : PoseContext :=
  step4NeighborsData[i.val]'(by change i.val < 64; exact i.isLt)

def step4SourcePoseIds : Fin 7 → Fin poseCount :=
  ![2272, 2274, 2276, 2278, 2280, 2282, 2284]
def step4SourceBlockIds : Fin 7 → Nat :=
  ![168, 169, 170, 171, 172, 173, 174]
def step4NeighborPoseIds : Fin 64 → Fin poseCount :=
  ![1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691]

def step4Plans : List Plan := [
  ⟨2260,none,[2290]⟩,
  ⟨2262,none,[2292]⟩,
  ⟨2264,none,[2294]⟩,
  ⟨2266,none,[2296]⟩,
  ⟨2268,none,[2298]⟩,
  ⟨2270,none,[2300]⟩,
  ⟨2272,some 168,[2302]⟩,
  ⟨2274,some 169,[2304]⟩,
  ⟨2276,some 170,[2306]⟩,
  ⟨2278,some 171,[2308]⟩,
  ⟨2280,some 172,[2310]⟩,
  ⟨2282,some 173,[]⟩,
  ⟨2284,some 174,[]⟩,
  ⟨2287,none,[2312]⟩,
]

def step4Pieces : List (Fin poseCount) := [2290, 2292, 2294, 2296, 2298, 2300, 2302, 2304, 2306, 2308, 2310, 2312]
def step4Links : List (Fin 927) := [332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343]

def step4PairCheck (i : Fin 7) (j : Fin 64) : Prop :=
  (step4Sources i).PairCheck (step4Neighbors j)

instance (i : Fin 7) (j : Fin 64) :
    Decidable (step4PairCheck i j) :=
  inferInstanceAs (Decidable ((step4Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
