import Compact.Cases.C898.CachedPairs.Contexts00
import Compact.Cases.C898.CachedPairs.Contexts01
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step0SourcesData : Array PoseContext := #[
  route0, route60, route61, route62, route63, route64, route65, route66, route67, route68, route69, route70, route71, route72, route73, route74, route75, route76, route77, route78, route79, route80, route81, route82, route83, route84, route85, route86, route87, route88, route89, route90, route91, route92, route93, route94, route95, route96, route97, route98, route99, route100, route101, route102, route103, route104, route105, route106, route107, route108
]

def step0Sources (i : Fin 50) : PoseContext :=
  step0SourcesData[i.val]'(by change i.val < 50; exact i.isLt)

def step0NeighborsData : Array PoseContext := #[
  route1, route2, route3, route4, route5, route6, route7, route8, route9, route10, route11, route12, route13, route14, route15, route16, route17, route18, route19, route20, route21, route22, route23, route24, route25, route26, route27, route28, route29, route30, route31, route32, route33, route34, route35, route36, route37, route38, route39, route40, route41, route42, route43, route44, route45, route46, route47, route48, route49, route50, route51, route52, route53, route54, route55, route56, route57, route58, route59
]

def step0Neighbors (i : Fin 59) : PoseContext :=
  step0NeighborsData[i.val]'(by change i.val < 59; exact i.isLt)

def step0SourcePoseIds : Fin 50 → Fin poseCount :=
  ![1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240]
def step0SourceBlockIds : Fin 50 → Nat :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49]
def step0NeighborPoseIds : Fin 59 → Fin poseCount :=
  ![1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568]

def step0Plans : List Plan := [
  ⟨1185,none,[1752]⟩,
  ⟨1186,none,[1754]⟩,
  ⟨1187,none,[1756]⟩,
  ⟨1188,none,[1758]⟩,
  ⟨1189,none,[1760]⟩,
  ⟨1190,none,[1762]⟩,
  ⟨1191,some 0,[1765, 1764]⟩,
  ⟨1192,some 1,[1769, 1768, 1767]⟩,
  ⟨1193,some 2,[1773, 1772, 1771]⟩,
  ⟨1194,some 3,[1778, 1777, 1776, 1775]⟩,
  ⟨1195,some 4,[1783, 1782, 1781, 1780]⟩,
  ⟨1196,some 5,[1788, 1787, 1786, 1785]⟩,
  ⟨1197,some 6,[1793, 1792, 1791, 1790]⟩,
  ⟨1198,some 7,[1797, 1796, 1795]⟩,
  ⟨1199,some 8,[1800, 1799]⟩,
  ⟨1200,some 9,[1802]⟩,
  ⟨1201,some 10,[1804]⟩,
  ⟨1202,some 11,[1806]⟩,
  ⟨1203,some 12,[1808]⟩,
  ⟨1204,some 13,[1810]⟩,
  ⟨1205,some 14,[1813, 1812]⟩,
  ⟨1206,some 15,[1817, 1816, 1815]⟩,
  ⟨1207,some 16,[1820, 1819]⟩,
  ⟨1208,some 17,[1823, 1822]⟩,
  ⟨1209,some 18,[1826, 1825]⟩,
  ⟨1210,some 19,[1829, 1828]⟩,
  ⟨1211,some 20,[1832, 1831]⟩,
  ⟨1212,some 21,[1835, 1834]⟩,
  ⟨1213,some 22,[1838, 1837]⟩,
  ⟨1214,some 23,[1841, 1840]⟩,
  ⟨1215,some 24,[1844, 1843]⟩,
  ⟨1216,some 25,[1847, 1846]⟩,
  ⟨1217,some 26,[1850, 1849]⟩,
  ⟨1218,some 27,[1853, 1852]⟩,
  ⟨1219,some 28,[1857, 1856, 1855]⟩,
  ⟨1220,some 29,[1861, 1860, 1859]⟩,
  ⟨1221,some 30,[1865, 1864, 1863]⟩,
  ⟨1222,some 31,[1869, 1868, 1867]⟩,
  ⟨1223,some 32,[1873, 1872, 1871]⟩,
  ⟨1224,some 33,[1876, 1875]⟩,
  ⟨1225,some 34,[1878]⟩,
  ⟨1226,some 35,[1880]⟩,
  ⟨1227,some 36,[1882]⟩,
  ⟨1228,some 37,[1884]⟩,
  ⟨1229,some 38,[1886]⟩,
  ⟨1230,some 39,[1888]⟩,
  ⟨1231,some 40,[1890]⟩,
  ⟨1232,some 41,[1892]⟩,
  ⟨1233,some 42,[1894]⟩,
  ⟨1234,some 43,[1896]⟩,
  ⟨1235,some 44,[1898]⟩,
  ⟨1236,some 45,[1900]⟩,
  ⟨1237,some 46,[1902]⟩,
  ⟨1238,some 47,[1904]⟩,
  ⟨1239,some 48,[1906]⟩,
  ⟨1240,some 49,[1908]⟩,
  ⟨1241,none,[1910]⟩,
  ⟨1242,none,[1912]⟩,
  ⟨1243,none,[1914]⟩,
  ⟨1244,none,[1916]⟩,
  ⟨1245,none,[1918]⟩,
  ⟨1246,none,[1920]⟩,
  ⟨1247,none,[1922]⟩,
  ⟨1248,none,[1924]⟩,
]

def step0Pieces : List (Fin poseCount) := [1752, 1754, 1756, 1758, 1760, 1762, 1765, 1764, 1769, 1768, 1767, 1773, 1772, 1771, 1778, 1777, 1776, 1775, 1783, 1782, 1781, 1780, 1788, 1787, 1786, 1785, 1793, 1792, 1791, 1790, 1797, 1796, 1795, 1800, 1799, 1802, 1804, 1806, 1808, 1810, 1813, 1812, 1817, 1816, 1815, 1820, 1819, 1823, 1822, 1826, 1825, 1829, 1828, 1832, 1831, 1835, 1834, 1838, 1837, 1841, 1840, 1844, 1843, 1847, 1846, 1850, 1849, 1853, 1852, 1857, 1856, 1855, 1861, 1860, 1859, 1865, 1864, 1863, 1869, 1868, 1867, 1873, 1872, 1871, 1876, 1875, 1878, 1880, 1882, 1884, 1886, 1888, 1890, 1892, 1894, 1896, 1898, 1900, 1902, 1904, 1906, 1908, 1910, 1912, 1914, 1916, 1918, 1920, 1922, 1924]
def step0Links : List (Fin 927) := [0, 1, 2, 3, 4, 5, 7, 6, 10, 9, 8, 13, 12, 11, 17, 16, 15, 14, 21, 20, 19, 18, 25, 24, 23, 22, 29, 28, 27, 26, 32, 31, 30, 34, 33, 35, 36, 37, 38, 39, 41, 40, 44, 43, 42, 46, 45, 48, 47, 50, 49, 52, 51, 54, 53, 56, 55, 58, 57, 60, 59, 62, 61, 64, 63, 66, 65, 68, 67, 71, 70, 69, 74, 73, 72, 77, 76, 75, 80, 79, 78, 83, 82, 81, 85, 84, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109]

def step0PairCheck (i : Fin 50) (j : Fin 59) : Prop :=
  (step0Sources i).PairCheck (step0Neighbors j)

instance (i : Fin 50) (j : Fin 59) :
    Decidable (step0PairCheck i j) :=
  inferInstanceAs (Decidable ((step0Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
