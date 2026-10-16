import Compact.Cases.C898.CachedPairs.Contexts06
import Compact.Cases.C898.CachedPairs.Contexts07
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step5SourcesData : Array PoseContext := #[
  route421, route434, route435, route436, route437, route438, route439, route440, route441, route442, route443, route444, route445, route446, route447, route448, route449, route450, route451, route452, route453, route454, route455, route456, route457, route458, route459, route460, route461, route462, route463, route464, route465, route466, route467, route468, route469, route470, route471, route472, route473, route474, route475, route476, route477, route478, route479, route480, route481, route482, route483
]

def step5Sources (i : Fin 51) : PoseContext :=
  step5SourcesData[i.val]'(by change i.val < 51; exact i.isLt)

def step5NeighborsData : Array PoseContext := #[
  route422, route423, route424, route425, route426, route427, route428, route429, route430, route431, route432, route433
]

def step5Neighbors (i : Fin 12) : PoseContext :=
  step5NeighborsData[i.val]'(by change i.val < 12; exact i.isLt)

def step5SourcePoseIds : Fin 51 → Fin poseCount :=
  ![1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508]
def step5SourceBlockIds : Fin 51 → Nat :=
  ![175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225]
def step5NeighborPoseIds : Fin 12 → Fin poseCount :=
  ![2289, 2291, 2293, 2295, 2297, 2299, 2301, 2303, 2305, 2307, 2309, 2311]

def step5Plans : List Plan := [
  ⟨1446,none,[2314]⟩,
  ⟨1447,none,[2316]⟩,
  ⟨1448,none,[2318]⟩,
  ⟨1449,none,[2320]⟩,
  ⟨1450,none,[2322]⟩,
  ⟨1451,none,[2324]⟩,
  ⟨1452,none,[2326]⟩,
  ⟨1453,none,[2328]⟩,
  ⟨1454,none,[2330]⟩,
  ⟨1455,none,[2332]⟩,
  ⟨1456,none,[2334]⟩,
  ⟨1457,none,[2336]⟩,
  ⟨1458,some 175,[2338]⟩,
  ⟨1459,some 176,[2340]⟩,
  ⟨1460,some 177,[2342]⟩,
  ⟨1461,some 178,[2344]⟩,
  ⟨1462,some 179,[2346]⟩,
  ⟨1463,some 180,[2348]⟩,
  ⟨1464,some 181,[2350]⟩,
  ⟨1465,some 182,[2352]⟩,
  ⟨1466,some 183,[2354]⟩,
  ⟨1467,some 184,[2356]⟩,
  ⟨1468,some 185,[2358]⟩,
  ⟨1469,some 186,[2360]⟩,
  ⟨1470,some 187,[2362]⟩,
  ⟨1471,some 188,[2364]⟩,
  ⟨1472,some 189,[2367, 2366]⟩,
  ⟨1473,some 190,[2370, 2369]⟩,
  ⟨1474,some 191,[2373, 2372]⟩,
  ⟨1475,some 192,[]⟩,
  ⟨1476,some 193,[2375]⟩,
  ⟨1477,some 194,[2377]⟩,
  ⟨1478,some 195,[2379]⟩,
  ⟨1479,some 196,[2381]⟩,
  ⟨1480,some 197,[2383]⟩,
  ⟨1481,some 198,[2385]⟩,
  ⟨1482,some 199,[2387]⟩,
  ⟨1483,some 200,[2389]⟩,
  ⟨1484,some 201,[2391]⟩,
  ⟨1485,some 202,[2393]⟩,
  ⟨1486,some 203,[2395]⟩,
  ⟨1487,some 204,[2397]⟩,
  ⟨1488,some 205,[2400, 2399]⟩,
  ⟨1489,some 206,[2403, 2402]⟩,
  ⟨1490,some 207,[2406, 2405]⟩,
  ⟨1491,some 208,[2409, 2408]⟩,
  ⟨1492,some 209,[2412, 2411]⟩,
  ⟨1493,some 210,[2415, 2414]⟩,
  ⟨1494,some 211,[2418, 2417]⟩,
  ⟨1495,some 212,[2421, 2420]⟩,
  ⟨1496,some 213,[2424, 2423]⟩,
  ⟨1497,some 214,[2427, 2426]⟩,
  ⟨1498,some 215,[2430, 2429]⟩,
  ⟨1499,some 216,[2433, 2432]⟩,
  ⟨1500,some 217,[2436, 2435]⟩,
  ⟨1501,some 218,[2439, 2438]⟩,
  ⟨1502,some 219,[2441]⟩,
  ⟨1503,some 220,[2443]⟩,
  ⟨1504,some 221,[2445]⟩,
  ⟨1505,some 222,[2447]⟩,
  ⟨1506,some 223,[2449]⟩,
  ⟨1507,some 224,[2451]⟩,
  ⟨1508,some 225,[2453]⟩,
  ⟨1509,none,[2455]⟩,
]

def step5Pieces : List (Fin poseCount) := [2314, 2316, 2318, 2320, 2322, 2324, 2326, 2328, 2330, 2332, 2334, 2336, 2338, 2340, 2342, 2344, 2346, 2348, 2350, 2352, 2354, 2356, 2358, 2360, 2362, 2364, 2367, 2366, 2370, 2369, 2373, 2372, 2375, 2377, 2379, 2381, 2383, 2385, 2387, 2389, 2391, 2393, 2395, 2397, 2400, 2399, 2403, 2402, 2406, 2405, 2409, 2408, 2412, 2411, 2415, 2414, 2418, 2417, 2421, 2420, 2424, 2423, 2427, 2426, 2430, 2429, 2433, 2432, 2436, 2435, 2439, 2438, 2441, 2443, 2445, 2447, 2449, 2451, 2453, 2455]
def step5Links : List (Fin 927) := [344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 371, 370, 373, 372, 375, 374, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 389, 388, 391, 390, 393, 392, 395, 394, 397, 396, 399, 398, 401, 400, 403, 402, 405, 404, 407, 406, 409, 408, 411, 410, 413, 412, 415, 414, 416, 417, 418, 419, 420, 421, 422, 423]

def step5PairCheck (i : Fin 51) (j : Fin 12) : Prop :=
  (step5Sources i).PairCheck (step5Neighbors j)

instance (i : Fin 51) (j : Fin 12) :
    Decidable (step5PairCheck i j) :=
  inferInstanceAs (Decidable ((step5Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
