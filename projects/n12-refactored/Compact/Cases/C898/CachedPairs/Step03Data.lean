import Compact.Cases.C898.CachedPairs.Contexts05
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

def step3SourcesData : Array PoseContext := #[
  route343, route408, route409, route410, route411, route412, route413
]

def step3Sources (i : Fin 7) : PoseContext :=
  step3SourcesData[i.val]'(by change i.val < 7; exact i.isLt)

def step3NeighborsData : Array PoseContext := #[
  route344, route345, route346, route347, route348, route349, route350, route351, route352, route353, route354, route355, route356, route357, route358, route359, route360, route361, route362, route363, route364, route365, route366, route367, route368, route369, route370, route371, route372, route373, route374, route375, route376, route377, route378, route379, route380, route381, route382, route383, route384, route385, route386, route387, route388, route389, route390, route391, route392, route393, route394, route395, route396, route397, route398, route399, route400, route401, route402, route403, route404, route405, route406, route407
]

def step3Neighbors (i : Fin 64) : PoseContext :=
  step3NeighborsData[i.val]'(by change i.val < 64; exact i.isLt)

def step3SourcePoseIds : Fin 7 → Fin poseCount :=
  ![1438, 1439, 1440, 1441, 1442, 1443, 1444]
def step3SourceBlockIds : Fin 7 → Nat :=
  ![161, 162, 163, 164, 165, 166, 167]
def step3NeighborPoseIds : Fin 64 → Fin poseCount :=
  ![2082, 2084, 2086, 2088, 2090, 2092, 2094, 2096, 2099, 2104, 2110, 2116, 2121, 2123, 2125, 2127, 2129, 2131, 2133, 2135, 2139, 2142, 2145, 2148, 2150, 2153, 2156, 2158, 2161, 2164, 2167, 2170, 2173, 2176, 2180, 2183, 2187, 2190, 2193, 2196, 2199, 2202, 2205, 2208, 2211, 2214, 2217, 2220, 2223, 2226, 2229, 2232, 2235, 2238, 2240, 2242, 2244, 2246, 2248, 2250, 2252, 2254, 2256, 2258]

def step3Plans : List Plan := [
  ⟨1430,none,[2261]⟩,
  ⟨1431,none,[2263]⟩,
  ⟨1432,none,[2265]⟩,
  ⟨1433,none,[2267]⟩,
  ⟨1434,none,[2269]⟩,
  ⟨1435,none,[2271]⟩,
  ⟨1436,none,[2273]⟩,
  ⟨1437,none,[2275]⟩,
  ⟨1438,some 161,[2277]⟩,
  ⟨1439,some 162,[2279]⟩,
  ⟨1440,some 163,[2281]⟩,
  ⟨1441,some 164,[2283]⟩,
  ⟨1442,some 165,[2286, 2285]⟩,
  ⟨1443,some 166,[]⟩,
  ⟨1444,some 167,[]⟩,
  ⟨1445,none,[2288]⟩,
]

def step3Pieces : List (Fin poseCount) := [2261, 2263, 2265, 2267, 2269, 2271, 2273, 2275, 2277, 2279, 2281, 2283, 2286, 2285, 2288]
def step3Links : List (Fin 927) := [317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 330, 329, 331]

def step3PairCheck (i : Fin 7) (j : Fin 64) : Prop :=
  (step3Sources i).PairCheck (step3Neighbors j)

instance (i : Fin 7) (j : Fin 64) :
    Decidable (step3PairCheck i j) :=
  inferInstanceAs (Decidable ((step3Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
