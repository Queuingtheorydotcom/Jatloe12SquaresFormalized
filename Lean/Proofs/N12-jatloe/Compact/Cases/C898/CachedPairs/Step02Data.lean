import Compact.Cases.C898.CachedPairs.Contexts03
import Compact.Cases.C898.CachedPairs.Contexts04
import Compact.Cases.C898.CachedPairs.Contexts05
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step2SourcesData : Array PoseContext := #[
  route237, route297, route298, route299, route300, route301, route302, route303, route304, route305, route306, route307, route308, route309, route310, route311, route312, route313, route314, route315, route316, route317, route318, route319, route320, route321, route322, route323, route324, route325, route326, route327, route328, route329, route330, route331, route332, route333, route334, route335, route336, route337, route338, route339, route340, route341, route342
]

def step2Sources (i : Fin 47) : PoseContext :=
  step2SourcesData[i.val]'(by change i.val < 47; exact i.isLt)

def step2NeighborsData : Array PoseContext := #[
  route238, route239, route240, route241, route242, route243, route244, route245, route246, route247, route248, route249, route250, route251, route252, route253, route254, route255, route256, route257, route258, route259, route260, route261, route262, route263, route264, route265, route266, route267, route268, route269, route270, route271, route272, route273, route274, route275, route276, route277, route278, route279, route280, route281, route282, route283, route284, route285, route286, route287, route288, route289, route290, route291, route292, route293, route294, route295, route296
]

def step2Neighbors (i : Fin 59) : PoseContext :=
  step2NeighborsData[i.val]'(by change i.val < 59; exact i.isLt)

def step2SourcePoseIds : Fin 47 → Fin poseCount :=
  ![1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365]
def step2SourceBlockIds : Fin 47 → Nat :=
  ![114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160]
def step2NeighborPoseIds : Fin 59 → Fin poseCount :=
  ![1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750]

def step2Plans : List Plan := [
  ⟨1313,none,[2083]⟩,
  ⟨1314,none,[2085]⟩,
  ⟨1315,none,[2087]⟩,
  ⟨1316,none,[2089]⟩,
  ⟨1317,none,[2091]⟩,
  ⟨1318,none,[2093]⟩,
  ⟨1319,some 114,[2095]⟩,
  ⟨1320,some 115,[2098, 2097]⟩,
  ⟨1321,some 116,[2103, 2102, 2101, 2100]⟩,
  ⟨1322,some 117,[2109, 2108, 2107, 2106, 2105]⟩,
  ⟨1323,some 118,[2115, 2114, 2113, 2112, 2111]⟩,
  ⟨1324,some 119,[2120, 2119, 2118, 2117]⟩,
  ⟨1325,some 120,[2122]⟩,
  ⟨1326,some 121,[2124]⟩,
  ⟨1327,some 122,[2126]⟩,
  ⟨1328,some 123,[2128]⟩,
  ⟨1329,some 124,[2130]⟩,
  ⟨1330,some 125,[2132]⟩,
  ⟨1331,some 126,[2134]⟩,
  ⟨1332,some 127,[2138, 2137, 2136]⟩,
  ⟨1333,some 128,[2141, 2140]⟩,
  ⟨1334,some 129,[2144, 2143]⟩,
  ⟨1335,some 130,[2147, 2146]⟩,
  ⟨1336,some 131,[2149]⟩,
  ⟨1337,some 132,[2152, 2151]⟩,
  ⟨1338,some 133,[2155, 2154]⟩,
  ⟨1339,some 134,[2157]⟩,
  ⟨1340,some 135,[2160, 2159]⟩,
  ⟨1341,some 136,[2163, 2162]⟩,
  ⟨1342,some 137,[2166, 2165]⟩,
  ⟨1343,some 138,[2169, 2168]⟩,
  ⟨1344,some 139,[2172, 2171]⟩,
  ⟨1345,some 140,[2175, 2174]⟩,
  ⟨1346,some 141,[2179, 2178, 2177]⟩,
  ⟨1347,some 142,[2182, 2181]⟩,
  ⟨1348,some 143,[2186, 2185, 2184]⟩,
  ⟨1349,some 144,[2189, 2188]⟩,
  ⟨1350,some 145,[2192, 2191]⟩,
  ⟨1351,some 146,[2195, 2194]⟩,
  ⟨1352,some 147,[2198, 2197]⟩,
  ⟨1353,some 148,[2201, 2200]⟩,
  ⟨1354,some 149,[2204, 2203]⟩,
  ⟨1355,some 150,[2207, 2206]⟩,
  ⟨1356,some 151,[2210, 2209]⟩,
  ⟨1357,some 152,[2213, 2212]⟩,
  ⟨1358,some 153,[2216, 2215]⟩,
  ⟨1359,some 154,[2219, 2218]⟩,
  ⟨1360,some 155,[2222, 2221]⟩,
  ⟨1361,some 156,[2225, 2224]⟩,
  ⟨1362,some 157,[2228, 2227]⟩,
  ⟨1363,some 158,[2231, 2230]⟩,
  ⟨1364,some 159,[2234, 2233]⟩,
  ⟨1365,some 160,[2237, 2236]⟩,
  ⟨1366,none,[2239]⟩,
  ⟨1367,none,[2241]⟩,
  ⟨1368,none,[2243]⟩,
  ⟨1369,none,[2245]⟩,
  ⟨1370,none,[2247]⟩,
  ⟨1371,none,[2249]⟩,
  ⟨1372,none,[2251]⟩,
  ⟨1373,none,[2253]⟩,
  ⟨1374,none,[2255]⟩,
  ⟨1375,none,[2257]⟩,
  ⟨1376,none,[2259]⟩,
]

def step2Pieces : List (Fin poseCount) := [2083, 2085, 2087, 2089, 2091, 2093, 2095, 2098, 2097, 2103, 2102, 2101, 2100, 2109, 2108, 2107, 2106, 2105, 2115, 2114, 2113, 2112, 2111, 2120, 2119, 2118, 2117, 2122, 2124, 2126, 2128, 2130, 2132, 2134, 2138, 2137, 2136, 2141, 2140, 2144, 2143, 2147, 2146, 2149, 2152, 2151, 2155, 2154, 2157, 2160, 2159, 2163, 2162, 2166, 2165, 2169, 2168, 2172, 2171, 2175, 2174, 2179, 2178, 2177, 2182, 2181, 2186, 2185, 2184, 2189, 2188, 2192, 2191, 2195, 2194, 2198, 2197, 2201, 2200, 2204, 2203, 2207, 2206, 2210, 2209, 2213, 2212, 2216, 2215, 2219, 2218, 2222, 2221, 2225, 2224, 2228, 2227, 2231, 2230, 2234, 2233, 2237, 2236, 2239, 2241, 2243, 2245, 2247, 2249, 2251, 2253, 2255, 2257, 2259]
def step2Links : List (Fin 927) := [203, 204, 205, 206, 207, 208, 209, 211, 210, 215, 214, 213, 212, 220, 219, 218, 217, 216, 225, 224, 223, 222, 221, 229, 228, 227, 226, 230, 231, 232, 233, 234, 235, 236, 239, 238, 237, 241, 240, 243, 242, 245, 244, 246, 248, 247, 250, 249, 251, 253, 252, 255, 254, 257, 256, 259, 258, 261, 260, 263, 262, 266, 265, 264, 268, 267, 271, 270, 269, 273, 272, 275, 274, 277, 276, 279, 278, 281, 280, 283, 282, 285, 284, 287, 286, 289, 288, 291, 290, 293, 292, 295, 294, 297, 296, 299, 298, 301, 300, 303, 302, 305, 304, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316]

def step2PairCheck (i : Fin 47) (j : Fin 59) : Prop :=
  (step2Sources i).PairCheck (step2Neighbors j)

instance (i : Fin 47) (j : Fin 59) :
    Decidable (step2PairCheck i j) :=
  inferInstanceAs (Decidable ((step2Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
