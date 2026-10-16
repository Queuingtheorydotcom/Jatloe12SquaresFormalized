import Compact.Cases.C898.CachedPairs.Contexts01
import Compact.Cases.C898.CachedPairs.Contexts02
import Compact.Cases.C898.CachedPairs.Contexts03
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step1SourcesData : Array PoseContext := #[
  route109, route174, route175, route176, route177, route178, route179, route180, route181, route182, route183, route184, route185, route186, route187, route188, route189, route190, route191, route192, route193, route194, route195, route196, route197, route198, route199, route200, route201, route202, route203, route204, route205, route206, route207, route208, route209, route210, route211, route212, route213, route214, route215, route216, route217, route218, route219, route220, route221, route222, route223, route224, route225, route226, route227, route228, route229, route230, route231, route232, route233, route234, route235, route236
]

def step1Sources (i : Fin 64) : PoseContext :=
  step1SourcesData[i.val]'(by change i.val < 64; exact i.isLt)

def step1NeighborsData : Array PoseContext := #[
  route110, route111, route112, route113, route114, route115, route116, route117, route118, route119, route120, route121, route122, route123, route124, route125, route126, route127, route128, route129, route130, route131, route132, route133, route134, route135, route136, route137, route138, route139, route140, route141, route142, route143, route144, route145, route146, route147, route148, route149, route150, route151, route152, route153, route154, route155, route156, route157, route158, route159, route160, route161, route162, route163, route164, route165, route166, route167, route168, route169, route170, route171, route172, route173
]

def step1Neighbors (i : Fin 64) : PoseContext :=
  step1NeighborsData[i.val]'(by change i.val < 64; exact i.isLt)

def step1SourcePoseIds : Fin 64 → Fin poseCount :=
  ![1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312]
def step1SourceBlockIds : Fin 64 → Nat :=
  ![50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113]
def step1NeighborPoseIds : Fin 64 → Fin poseCount :=
  ![1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691]

def step1Plans : List Plan := [
  ⟨1249,some 50,[1926]⟩,
  ⟨1250,some 51,[1928]⟩,
  ⟨1251,some 52,[1930]⟩,
  ⟨1252,some 53,[1932]⟩,
  ⟨1253,some 54,[1934]⟩,
  ⟨1254,some 55,[1936]⟩,
  ⟨1255,some 56,[1938]⟩,
  ⟨1256,some 57,[1940]⟩,
  ⟨1257,some 58,[1942]⟩,
  ⟨1258,some 59,[1944]⟩,
  ⟨1259,some 60,[1946]⟩,
  ⟨1260,some 61,[1948]⟩,
  ⟨1261,some 62,[1950]⟩,
  ⟨1262,some 63,[1952]⟩,
  ⟨1263,some 64,[1954]⟩,
  ⟨1264,some 65,[1956]⟩,
  ⟨1265,some 66,[1958]⟩,
  ⟨1266,some 67,[1960]⟩,
  ⟨1267,some 68,[1962]⟩,
  ⟨1268,some 69,[1964]⟩,
  ⟨1269,some 70,[1966]⟩,
  ⟨1270,some 71,[1968]⟩,
  ⟨1271,some 72,[1970]⟩,
  ⟨1272,some 73,[1972]⟩,
  ⟨1273,some 74,[1974]⟩,
  ⟨1274,some 75,[1976]⟩,
  ⟨1275,some 76,[1978]⟩,
  ⟨1276,some 77,[1981, 1980]⟩,
  ⟨1277,some 78,[1984, 1983]⟩,
  ⟨1278,some 79,[1987, 1986]⟩,
  ⟨1279,some 80,[1990, 1989]⟩,
  ⟨1280,some 81,[1993, 1992]⟩,
  ⟨1281,some 82,[1996, 1995]⟩,
  ⟨1282,some 83,[1999, 1998]⟩,
  ⟨1283,some 84,[2002, 2001]⟩,
  ⟨1284,some 85,[2005, 2004]⟩,
  ⟨1285,some 86,[2008, 2007]⟩,
  ⟨1286,some 87,[2011, 2010]⟩,
  ⟨1287,some 88,[2014, 2013]⟩,
  ⟨1288,some 89,[2017, 2016]⟩,
  ⟨1289,some 90,[2020, 2019]⟩,
  ⟨1290,some 91,[2023, 2022]⟩,
  ⟨1291,some 92,[2026, 2025]⟩,
  ⟨1292,some 93,[2029, 2028]⟩,
  ⟨1293,some 94,[2032, 2031]⟩,
  ⟨1294,some 95,[2035, 2034]⟩,
  ⟨1295,some 96,[2038, 2037]⟩,
  ⟨1296,some 97,[2041, 2040]⟩,
  ⟨1297,some 98,[2044, 2043]⟩,
  ⟨1298,some 99,[2047, 2046]⟩,
  ⟨1299,some 100,[2050, 2049]⟩,
  ⟨1300,some 101,[2053, 2052]⟩,
  ⟨1301,some 102,[2056, 2055]⟩,
  ⟨1302,some 103,[2059, 2058]⟩,
  ⟨1303,some 104,[2062, 2061]⟩,
  ⟨1304,some 105,[2065, 2064]⟩,
  ⟨1305,some 106,[2067]⟩,
  ⟨1306,some 107,[2069]⟩,
  ⟨1307,some 108,[2071]⟩,
  ⟨1308,some 109,[2073]⟩,
  ⟨1309,some 110,[2075]⟩,
  ⟨1310,some 111,[2077]⟩,
  ⟨1311,some 112,[2079]⟩,
  ⟨1312,some 113,[2081]⟩,
]

def step1Pieces : List (Fin poseCount) := [1926, 1928, 1930, 1932, 1934, 1936, 1938, 1940, 1942, 1944, 1946, 1948, 1950, 1952, 1954, 1956, 1958, 1960, 1962, 1964, 1966, 1968, 1970, 1972, 1974, 1976, 1978, 1981, 1980, 1984, 1983, 1987, 1986, 1990, 1989, 1993, 1992, 1996, 1995, 1999, 1998, 2002, 2001, 2005, 2004, 2008, 2007, 2011, 2010, 2014, 2013, 2017, 2016, 2020, 2019, 2023, 2022, 2026, 2025, 2029, 2028, 2032, 2031, 2035, 2034, 2038, 2037, 2041, 2040, 2044, 2043, 2047, 2046, 2050, 2049, 2053, 2052, 2056, 2055, 2059, 2058, 2062, 2061, 2065, 2064, 2067, 2069, 2071, 2073, 2075, 2077, 2079, 2081]
def step1Links : List (Fin 927) := [110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 138, 137, 140, 139, 142, 141, 144, 143, 146, 145, 148, 147, 150, 149, 152, 151, 154, 153, 156, 155, 158, 157, 160, 159, 162, 161, 164, 163, 166, 165, 168, 167, 170, 169, 172, 171, 174, 173, 176, 175, 178, 177, 180, 179, 182, 181, 184, 183, 186, 185, 188, 187, 190, 189, 192, 191, 194, 193, 195, 196, 197, 198, 199, 200, 201, 202]

def step1PairCheck (i : Fin 64) (j : Fin 64) : Prop :=
  (step1Sources i).PairCheck (step1Neighbors j)

instance (i : Fin 64) (j : Fin 64) :
    Decidable (step1PairCheck i j) :=
  inferInstanceAs (Decidable ((step1Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
