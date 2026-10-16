import Compact.Cases.C898.CachedPairs.Contexts14
import Compact.Cases.C898.CachedPairs.Contexts15
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step13SourcesData : Array PoseContext := #[
  route916, route980, route981, route982, route983, route984, route985, route986, route987, route988, route989, route990, route991, route992, route993, route994, route995, route996, route997, route998, route999, route1000, route1001
]

def step13Sources (i : Fin 23) : PoseContext :=
  step13SourcesData[i.val]'(by change i.val < 23; exact i.isLt)

def step13NeighborsData : Array PoseContext := #[
  route917, route918, route919, route920, route921, route922, route923, route924, route925, route926, route927, route928, route929, route930, route931, route932, route933, route934, route935, route936, route937, route938, route939, route940, route941, route942, route943, route944, route945, route946, route947, route948, route949, route950, route951, route952, route953, route954, route955, route956, route957, route958, route959, route960, route961, route962, route963, route964, route965, route966, route967, route968, route969, route970, route971, route972, route973, route974, route975, route976, route977, route978, route979
]

def step13Neighbors (i : Fin 63) : PoseContext :=
  step13NeighborsData[i.val]'(by change i.val < 63; exact i.isLt)

def step13SourcePoseIds : Fin 23 → Fin poseCount :=
  ![3255, 3257, 3259, 3261, 3263, 3265, 3267, 3269, 3271, 3273, 3275, 3277, 3279, 3281, 3283, 3285, 3287, 3289, 3291, 3293, 3295, 3297, 3299]
def step13SourceBlockIds : Fin 23 → Nat :=
  ![469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491]
def step13NeighborPoseIds : Fin 63 → Fin poseCount :=
  ![2456, 2458, 2460, 2463, 2466, 2469, 2472, 2475, 2478, 2481, 2484, 2487, 2490, 2493, 2496, 2499, 2502, 2505, 2508, 2512, 2514, 2516, 2518, 2520, 2522, 2524, 2526, 2528, 2530, 2532, 2534, 2536, 2538, 2540, 2542, 2544, 2546, 2548, 2550, 2553, 2556, 2559, 2562, 2565, 2568, 2571, 2574, 2577, 2580, 2583, 2586, 2590, 2594, 2598, 2602, 2606, 2609, 2612, 2615, 2618, 2621, 2624, 2627]

def step13Plans : List Plan := [
  ⟨3255,some 469,[3302]⟩,
  ⟨3257,some 470,[3304]⟩,
  ⟨3259,some 471,[3306]⟩,
  ⟨3261,some 472,[3308]⟩,
  ⟨3263,some 473,[3310]⟩,
  ⟨3265,some 474,[3312]⟩,
  ⟨3267,some 475,[3314]⟩,
  ⟨3269,some 476,[3316]⟩,
  ⟨3271,some 477,[]⟩,
  ⟨3273,some 478,[]⟩,
  ⟨3275,some 479,[]⟩,
  ⟨3277,some 480,[]⟩,
  ⟨3279,some 481,[]⟩,
  ⟨3281,some 482,[]⟩,
  ⟨3283,some 483,[]⟩,
  ⟨3285,some 484,[]⟩,
  ⟨3287,some 485,[]⟩,
  ⟨3289,some 486,[]⟩,
  ⟨3291,some 487,[]⟩,
  ⟨3293,some 488,[]⟩,
  ⟨3295,some 489,[]⟩,
  ⟨3297,some 490,[]⟩,
  ⟨3299,some 491,[]⟩,
]

def step13Pieces : List (Fin poseCount) := [3302, 3304, 3306, 3308, 3310, 3312, 3314, 3316]
def step13Links : List (Fin 927) := [919, 920, 921, 922, 923, 924, 925, 926]

def step13PairCheck (i : Fin 23) (j : Fin 63) : Prop :=
  (step13Sources i).PairCheck (step13Neighbors j)

instance (i : Fin 23) (j : Fin 63) :
    Decidable (step13PairCheck i j) :=
  inferInstanceAs (Decidable ((step13Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
