import Compact.Cases.C898.CachedPairs.Contexts03
import Compact.Cases.C898.CachedPairs.Contexts04
import Compact.Cases.C898.CachedPairs.Contexts07
import Compact.Cases.C898.CachedPairs.Contexts08
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step6SourcesData : Array PoseContext := #[
  route484, route485, route486, route487, route488, route489, route490, route491, route492, route493, route494, route495, route496, route497, route498, route499, route500, route501, route502, route503, route504, route505, route506, route507, route508, route509, route510, route511, route512, route513, route514, route515, route516, route517, route518, route519, route520, route521, route522, route523, route524, route525, route526, route527, route528, route529, route530, route531, route532, route533, route534, route535, route536, route537, route538, route539, route540, route541, route542
]

def step6Sources (i : Fin 59) : PoseContext :=
  step6SourcesData[i.val]'(by change i.val < 59; exact i.isLt)

def step6NeighborsData : Array PoseContext := #[
  route238, route239, route240, route241, route242, route243, route244, route245, route246, route247, route248, route249, route250, route251, route252, route253, route254, route255, route256, route257, route258, route259, route260, route261, route262, route263, route264, route265, route266, route267, route268, route269, route270, route271, route272, route273, route274, route275, route276, route277, route278, route279, route280, route281, route282, route283, route284, route285, route286, route287, route288, route289, route290, route291, route292, route293, route294, route295, route296
]

def step6Neighbors (i : Fin 59) : PoseContext :=
  step6NeighborsData[i.val]'(by change i.val < 59; exact i.isLt)

def step6SourcePoseIds : Fin 59 → Fin poseCount :=
  ![2317, 2319, 2321, 2323, 2325, 2327, 2329, 2331, 2333, 2335, 2337, 2339, 2341, 2343, 2345, 2347, 2349, 2351, 2353, 2355, 2357, 2359, 2361, 2363, 2365, 2368, 2371, 2376, 2378, 2380, 2382, 2384, 2386, 2388, 2390, 2392, 2394, 2396, 2398, 2401, 2404, 2407, 2410, 2413, 2416, 2419, 2422, 2425, 2428, 2431, 2434, 2437, 2440, 2442, 2444, 2446, 2448, 2450, 2452]
def step6SourceBlockIds : Fin 59 → Nat :=
  ![226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284]
def step6NeighborPoseIds : Fin 59 → Fin poseCount :=
  ![1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750]

def step6Plans : List Plan := [
  ⟨2313,none,[2457]⟩,
  ⟨2315,none,[2459]⟩,
  ⟨2317,some 226,[2462, 2461]⟩,
  ⟨2319,some 227,[2465, 2464]⟩,
  ⟨2321,some 228,[2468, 2467]⟩,
  ⟨2323,some 229,[2471, 2470]⟩,
  ⟨2325,some 230,[2474, 2473]⟩,
  ⟨2327,some 231,[2477, 2476]⟩,
  ⟨2329,some 232,[2480, 2479]⟩,
  ⟨2331,some 233,[2483, 2482]⟩,
  ⟨2333,some 234,[2486, 2485]⟩,
  ⟨2335,some 235,[2489, 2488]⟩,
  ⟨2337,some 236,[2492, 2491]⟩,
  ⟨2339,some 237,[2495, 2494]⟩,
  ⟨2341,some 238,[2498, 2497]⟩,
  ⟨2343,some 239,[2501, 2500]⟩,
  ⟨2345,some 240,[2504, 2503]⟩,
  ⟨2347,some 241,[2507, 2506]⟩,
  ⟨2349,some 242,[2511, 2510, 2509]⟩,
  ⟨2351,some 243,[2513]⟩,
  ⟨2353,some 244,[2515]⟩,
  ⟨2355,some 245,[2517]⟩,
  ⟨2357,some 246,[2519]⟩,
  ⟨2359,some 247,[2521]⟩,
  ⟨2361,some 248,[2523]⟩,
  ⟨2363,some 249,[2525]⟩,
  ⟨2365,some 250,[2527]⟩,
  ⟨2368,some 251,[2529]⟩,
  ⟨2371,some 252,[2531]⟩,
  ⟨2374,none,[2533]⟩,
  ⟨2376,some 253,[2535]⟩,
  ⟨2378,some 254,[2537]⟩,
  ⟨2380,some 255,[2539]⟩,
  ⟨2382,some 256,[2541]⟩,
  ⟨2384,some 257,[2543]⟩,
  ⟨2386,some 258,[2545]⟩,
  ⟨2388,some 259,[2547]⟩,
  ⟨2390,some 260,[2549]⟩,
  ⟨2392,some 261,[2552, 2551]⟩,
  ⟨2394,some 262,[2555, 2554]⟩,
  ⟨2396,some 263,[2558, 2557]⟩,
  ⟨2398,some 264,[2561, 2560]⟩,
  ⟨2401,some 265,[2564, 2563]⟩,
  ⟨2404,some 266,[2567, 2566]⟩,
  ⟨2407,some 267,[2570, 2569]⟩,
  ⟨2410,some 268,[2573, 2572]⟩,
  ⟨2413,some 269,[2576, 2575]⟩,
  ⟨2416,some 270,[2579, 2578]⟩,
  ⟨2419,some 271,[2582, 2581]⟩,
  ⟨2422,some 272,[2585, 2584]⟩,
  ⟨2425,some 273,[2589, 2588, 2587]⟩,
  ⟨2428,some 274,[2593, 2592, 2591]⟩,
  ⟨2431,some 275,[2597, 2596, 2595]⟩,
  ⟨2434,some 276,[2601, 2600, 2599]⟩,
  ⟨2437,some 277,[2605, 2604, 2603]⟩,
  ⟨2440,some 278,[2608, 2607]⟩,
  ⟨2442,some 279,[2611, 2610]⟩,
  ⟨2444,some 280,[2614, 2613]⟩,
  ⟨2446,some 281,[2617, 2616]⟩,
  ⟨2448,some 282,[2620, 2619]⟩,
  ⟨2450,some 283,[2623, 2622]⟩,
  ⟨2452,some 284,[2626, 2625]⟩,
  ⟨2454,none,[2628]⟩,
]

def step6Pieces : List (Fin poseCount) := [2457, 2459, 2462, 2461, 2465, 2464, 2468, 2467, 2471, 2470, 2474, 2473, 2477, 2476, 2480, 2479, 2483, 2482, 2486, 2485, 2489, 2488, 2492, 2491, 2495, 2494, 2498, 2497, 2501, 2500, 2504, 2503, 2507, 2506, 2511, 2510, 2509, 2513, 2515, 2517, 2519, 2521, 2523, 2525, 2527, 2529, 2531, 2533, 2535, 2537, 2539, 2541, 2543, 2545, 2547, 2549, 2552, 2551, 2555, 2554, 2558, 2557, 2561, 2560, 2564, 2563, 2567, 2566, 2570, 2569, 2573, 2572, 2576, 2575, 2579, 2578, 2582, 2581, 2585, 2584, 2589, 2588, 2587, 2593, 2592, 2591, 2597, 2596, 2595, 2601, 2600, 2599, 2605, 2604, 2603, 2608, 2607, 2611, 2610, 2614, 2613, 2617, 2616, 2620, 2619, 2623, 2622, 2626, 2625, 2628]
def step6Links : List (Fin 927) := [424, 425, 427, 426, 429, 428, 431, 430, 433, 432, 435, 434, 437, 436, 439, 438, 441, 440, 443, 442, 445, 444, 447, 446, 449, 448, 451, 450, 453, 452, 455, 454, 457, 456, 460, 459, 458, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 481, 480, 483, 482, 485, 484, 487, 486, 489, 488, 491, 490, 493, 492, 495, 494, 497, 496, 499, 498, 501, 500, 503, 502, 506, 505, 504, 509, 508, 507, 512, 511, 510, 515, 514, 513, 518, 517, 516, 520, 519, 522, 521, 524, 523, 526, 525, 528, 527, 530, 529, 532, 531, 533]

def step6PairCheck (i : Fin 59) (j : Fin 59) : Prop :=
  (step6Sources i).PairCheck (step6Neighbors j)

instance (i : Fin 59) (j : Fin 59) :
    Decidable (step6PairCheck i j) :=
  inferInstanceAs (Decidable ((step6Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
