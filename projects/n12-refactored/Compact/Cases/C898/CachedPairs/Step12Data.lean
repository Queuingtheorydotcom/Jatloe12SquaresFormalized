import Compact.Cases.C898.CachedPairs.Contexts06
import Compact.Cases.C898.CachedPairs.Contexts13
import Compact.Cases.C898.CachedPairs.Contexts14
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step12SourcesData : Array PoseContext := #[
  route867, route868, route869, route870, route871, route872, route873, route874, route875, route876, route877, route878, route879, route880, route881, route882, route883, route884, route885, route886, route887, route888, route889, route890, route891, route892, route893, route894, route895, route896, route897, route898, route899, route900, route901, route902, route903, route904, route905, route906, route907, route908, route909, route910, route911, route912, route913, route914, route915
]

def step12Sources (i : Fin 49) : PoseContext :=
  step12SourcesData[i.val]'(by change i.val < 49; exact i.isLt)

def step12NeighborsData : Array PoseContext := #[
  route422, route423, route424, route425, route426, route427, route428, route429, route430, route431, route432, route433
]

def step12Neighbors (i : Fin 12) : PoseContext :=
  step12NeighborsData[i.val]'(by change i.val < 12; exact i.isLt)

def step12SourcePoseIds : Fin 49 → Fin poseCount :=
  ![3154, 3157, 3160, 3162, 3164, 3166, 3169, 3171, 3173, 3175, 3177, 3179, 3181, 3183, 3185, 3187, 3189, 3191, 3193, 3195, 3197, 3199, 3201, 3203, 3205, 3207, 3209, 3211, 3213, 3215, 3217, 3219, 3221, 3223, 3225, 3227, 3229, 3231, 3233, 3235, 3237, 3239, 3241, 3243, 3245, 3247, 3249, 3251, 3253]
def step12SourceBlockIds : Fin 49 → Nat :=
  ![420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468]
def step12NeighborPoseIds : Fin 12 → Fin poseCount :=
  ![2289, 2291, 2293, 2295, 2297, 2299, 2301, 2303, 2305, 2307, 2309, 2311]

def step12Plans : List Plan := [
  ⟨3154,some 420,[]⟩,
  ⟨3157,some 421,[]⟩,
  ⟨3160,some 422,[]⟩,
  ⟨3162,some 423,[]⟩,
  ⟨3164,some 424,[]⟩,
  ⟨3166,some 425,[]⟩,
  ⟨3169,some 426,[]⟩,
  ⟨3171,some 427,[]⟩,
  ⟨3173,some 428,[]⟩,
  ⟨3175,some 429,[3256]⟩,
  ⟨3177,some 430,[3258]⟩,
  ⟨3179,some 431,[3260]⟩,
  ⟨3181,some 432,[3262]⟩,
  ⟨3183,some 433,[3264]⟩,
  ⟨3185,some 434,[3266]⟩,
  ⟨3187,some 435,[3268]⟩,
  ⟨3189,some 436,[3270]⟩,
  ⟨3191,some 437,[3272]⟩,
  ⟨3193,some 438,[3274]⟩,
  ⟨3195,some 439,[3276]⟩,
  ⟨3197,some 440,[3278]⟩,
  ⟨3199,some 441,[3280]⟩,
  ⟨3201,some 442,[3282]⟩,
  ⟨3203,some 443,[3284]⟩,
  ⟨3205,some 444,[3286]⟩,
  ⟨3207,some 445,[3288]⟩,
  ⟨3209,some 446,[3290]⟩,
  ⟨3211,some 447,[3292]⟩,
  ⟨3213,some 448,[3294]⟩,
  ⟨3215,some 449,[3296]⟩,
  ⟨3217,some 450,[3298]⟩,
  ⟨3219,some 451,[3300]⟩,
  ⟨3221,some 452,[]⟩,
  ⟨3223,some 453,[]⟩,
  ⟨3225,some 454,[]⟩,
  ⟨3227,some 455,[]⟩,
  ⟨3229,some 456,[]⟩,
  ⟨3231,some 457,[]⟩,
  ⟨3233,some 458,[]⟩,
  ⟨3235,some 459,[]⟩,
  ⟨3237,some 460,[]⟩,
  ⟨3239,some 461,[]⟩,
  ⟨3241,some 462,[]⟩,
  ⟨3243,some 463,[]⟩,
  ⟨3245,some 464,[]⟩,
  ⟨3247,some 465,[]⟩,
  ⟨3249,some 466,[]⟩,
  ⟨3251,some 467,[]⟩,
  ⟨3253,some 468,[]⟩,
]

def step12Pieces : List (Fin poseCount) := [3256, 3258, 3260, 3262, 3264, 3266, 3268, 3270, 3272, 3274, 3276, 3278, 3280, 3282, 3284, 3286, 3288, 3290, 3292, 3294, 3296, 3298, 3300]
def step12Links : List (Fin 927) := [896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918]

def step12PairCheck (i : Fin 49) (j : Fin 12) : Prop :=
  (step12Sources i).PairCheck (step12Neighbors j)

instance (i : Fin 49) (j : Fin 12) :
    Decidable (step12PairCheck i j) :=
  inferInstanceAs (Decidable ((step12Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
