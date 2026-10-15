import Compact.Cases.C898.CachedPairs.Contexts08
import Compact.Cases.C898.CachedPairs.Contexts09
import Compact.Cases.C898.CachedPairs.Contexts10
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step7SourcesData : Array PoseContext := #[
  route543, route608, route609, route610, route611, route612, route613, route614, route615, route616, route617, route618, route619, route620, route621, route622, route623, route624, route625, route626, route627, route628, route629, route630, route631, route632, route633, route634, route635, route636, route637, route638, route639, route640, route641, route642, route643, route644, route645, route646, route647, route648, route649, route650, route651, route652, route653, route654, route655
]

def step7Sources (i : Fin 49) : PoseContext :=
  step7SourcesData[i.val]'(by change i.val < 49; exact i.isLt)

def step7NeighborsData : Array PoseContext := #[
  route544, route545, route546, route547, route548, route549, route550, route551, route552, route553, route554, route555, route556, route557, route558, route559, route560, route561, route562, route563, route564, route565, route566, route567, route568, route569, route570, route571, route572, route573, route574, route575, route576, route577, route578, route579, route580, route581, route582, route583, route584, route585, route586, route587, route588, route589, route590, route591, route592, route593, route594, route595, route596, route597, route598, route599, route600, route601, route602, route603, route604, route605, route606, route607
]

def step7Neighbors (i : Fin 64) : PoseContext :=
  step7NeighborsData[i.val]'(by change i.val < 64; exact i.isLt)

def step7SourcePoseIds : Fin 49 → Fin poseCount :=
  ![1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621]
def step7SourceBlockIds : Fin 49 → Nat :=
  ![285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333]
def step7NeighborPoseIds : Fin 64 → Fin poseCount :=
  ![1925, 1927, 1929, 1931, 1933, 1935, 1937, 1939, 1941, 1943, 1945, 1947, 1949, 1951, 1953, 1955, 1957, 1959, 1961, 1963, 1965, 1967, 1969, 1971, 1973, 1975, 1977, 1979, 1982, 1985, 1988, 1991, 1994, 1997, 2000, 2003, 2006, 2009, 2012, 2015, 2018, 2021, 2024, 2027, 2030, 2033, 2036, 2039, 2042, 2045, 2048, 2051, 2054, 2057, 2060, 2063, 2066, 2068, 2070, 2072, 2074, 2076, 2078, 2080]

def step7Plans : List Plan := [
  ⟨1569,none,[2630]⟩,
  ⟨1570,none,[2632]⟩,
  ⟨1571,some 285,[2635, 2634]⟩,
  ⟨1572,some 286,[2638, 2637]⟩,
  ⟨1573,some 287,[2641, 2640]⟩,
  ⟨1574,some 288,[2644, 2643]⟩,
  ⟨1575,some 289,[2647, 2646]⟩,
  ⟨1576,some 290,[2650, 2649]⟩,
  ⟨1577,some 291,[2653, 2652]⟩,
  ⟨1578,some 292,[2656, 2655]⟩,
  ⟨1579,some 293,[2659, 2658]⟩,
  ⟨1580,some 294,[2662, 2661]⟩,
  ⟨1581,some 295,[2665, 2664]⟩,
  ⟨1582,some 296,[2668, 2667]⟩,
  ⟨1583,some 297,[2670]⟩,
  ⟨1584,some 298,[2672]⟩,
  ⟨1585,some 299,[2674]⟩,
  ⟨1586,some 300,[2676]⟩,
  ⟨1587,some 301,[2678]⟩,
  ⟨1588,some 302,[2680]⟩,
  ⟨1589,some 303,[]⟩,
  ⟨1590,some 304,[]⟩,
  ⟨1591,some 305,[]⟩,
  ⟨1592,some 306,[]⟩,
  ⟨1593,some 307,[]⟩,
  ⟨1594,some 308,[]⟩,
  ⟨1595,some 309,[2682]⟩,
  ⟨1596,some 310,[2684]⟩,
  ⟨1597,some 311,[2686]⟩,
  ⟨1598,some 312,[2688]⟩,
  ⟨1599,some 313,[2690]⟩,
  ⟨1600,some 314,[2692]⟩,
  ⟨1601,some 315,[2694]⟩,
  ⟨1602,some 316,[2696]⟩,
  ⟨1603,some 317,[2698]⟩,
  ⟨1604,some 318,[2700]⟩,
  ⟨1605,none,[2702]⟩,
  ⟨1606,none,[2704]⟩,
  ⟨1607,some 319,[2707, 2706]⟩,
  ⟨1608,some 320,[2710, 2709]⟩,
  ⟨1609,some 321,[2713, 2712]⟩,
  ⟨1610,some 322,[2716, 2715]⟩,
  ⟨1611,some 323,[2719, 2718]⟩,
  ⟨1612,some 324,[2722, 2721]⟩,
  ⟨1613,some 325,[2725, 2724]⟩,
  ⟨1614,some 326,[2728, 2727]⟩,
  ⟨1615,some 327,[2731, 2730]⟩,
  ⟨1616,some 328,[2734, 2733]⟩,
  ⟨1617,some 329,[2737, 2736]⟩,
  ⟨1618,some 330,[2740, 2739]⟩,
  ⟨1619,some 331,[2743, 2742]⟩,
  ⟨1620,some 332,[2746, 2745]⟩,
  ⟨1621,some 333,[2749, 2748]⟩,
  ⟨1622,none,[2751]⟩,
  ⟨1623,none,[2753]⟩,
  ⟨1624,none,[2755]⟩,
  ⟨1625,none,[2757]⟩,
  ⟨1626,none,[2759]⟩,
  ⟨1627,none,[2761]⟩,
]

def step7Pieces : List (Fin poseCount) := [2630, 2632, 2635, 2634, 2638, 2637, 2641, 2640, 2644, 2643, 2647, 2646, 2650, 2649, 2653, 2652, 2656, 2655, 2659, 2658, 2662, 2661, 2665, 2664, 2668, 2667, 2670, 2672, 2674, 2676, 2678, 2680, 2682, 2684, 2686, 2688, 2690, 2692, 2694, 2696, 2698, 2700, 2702, 2704, 2707, 2706, 2710, 2709, 2713, 2712, 2716, 2715, 2719, 2718, 2722, 2721, 2725, 2724, 2728, 2727, 2731, 2730, 2734, 2733, 2737, 2736, 2740, 2739, 2743, 2742, 2746, 2745, 2749, 2748, 2751, 2753, 2755, 2757, 2759, 2761]
def step7Links : List (Fin 927) := [534, 535, 537, 536, 539, 538, 541, 540, 543, 542, 545, 544, 547, 546, 549, 548, 551, 550, 553, 552, 555, 554, 557, 556, 559, 558, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 579, 578, 581, 580, 583, 582, 585, 584, 587, 586, 589, 588, 591, 590, 593, 592, 595, 594, 597, 596, 599, 598, 601, 600, 603, 602, 605, 604, 607, 606, 608, 609, 610, 611, 612, 613]

def step7PairCheck (i : Fin 49) (j : Fin 64) : Prop :=
  (step7Sources i).PairCheck (step7Neighbors j)

instance (i : Fin 49) (j : Fin 64) :
    Decidable (step7PairCheck i j) :=
  inferInstanceAs (Decidable ((step7Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
