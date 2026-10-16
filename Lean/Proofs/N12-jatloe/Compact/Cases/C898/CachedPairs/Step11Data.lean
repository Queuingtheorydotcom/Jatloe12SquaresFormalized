import Compact.Cases.C898.CachedPairs.Contexts12
import Compact.Cases.C898.CachedPairs.Contexts13
import Compact.Cases.C898.CachedPairPlans
import Compact.Cases.C898.PairComplements
import Compact.Cases.C898.SharedDomains

set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false

namespace N12Compact.C898Cached.AllPairs
open C898Shared CachedSupportFan S12
noncomputable section

def step11SourcesData : Array PoseContext := #[
  route784, route846, route847, route848, route849, route850, route851, route852, route853, route854, route855, route856, route857, route858, route859, route860, route861, route862, route863, route864, route865, route866
]

def step11Sources (i : Fin 22) : PoseContext :=
  step11SourcesData[i.val]'(by change i.val < 22; exact i.isLt)

def step11NeighborsData : Array PoseContext := #[
  route785, route786, route787, route788, route789, route790, route791, route792, route793, route794, route795, route796, route797, route798, route799, route800, route801, route802, route803, route804, route805, route806, route807, route808, route809, route810, route811, route812, route813, route814, route815, route816, route817, route818, route819, route820, route821, route822, route823, route824, route825, route826, route827, route828, route829, route830, route831, route832, route833, route834, route835, route836, route837, route838, route839, route840, route841, route842, route843, route844, route845
]

def step11Neighbors (i : Fin 61) : PoseContext :=
  step11NeighborsData[i.val]'(by change i.val < 61; exact i.isLt)

def step11SourcePoseIds : Fin 22 → Fin poseCount :=
  ![3056, 3058, 3060, 3062, 3064, 3066, 3068, 3070, 3072, 3074, 3076, 3078, 3080, 3082, 3084, 3086, 3088, 3090, 3092, 3094, 3096, 3098]
def step11SourceBlockIds : Fin 22 → Nat :=
  ![398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419]
def step11NeighborPoseIds : Fin 61 → Fin poseCount :=
  ![2762, 2773, 2783, 2791, 2799, 2804, 2808, 2810, 2812, 2814, 2816, 2818, 2820, 2822, 2824, 2826, 2828, 2830, 2832, 2834, 2836, 2838, 2840, 2842, 2844, 2846, 2848, 2850, 2852, 2854, 2856, 2858, 2860, 2862, 2864, 2866, 2868, 2870, 2872, 2874, 2876, 2878, 2880, 2882, 2884, 2886, 2888, 2890, 2892, 2894, 2896, 2898, 2900, 2902, 2904, 2906, 2910, 2918, 2925, 2932, 2942]

def step11Plans : List Plan := [
  ⟨3056,some 398,[3156, 3155]⟩,
  ⟨3058,some 399,[3159, 3158]⟩,
  ⟨3060,some 400,[3161]⟩,
  ⟨3062,some 401,[3163]⟩,
  ⟨3064,some 402,[3165]⟩,
  ⟨3066,some 403,[3168, 3167]⟩,
  ⟨3068,some 404,[3170]⟩,
  ⟨3070,some 405,[3172]⟩,
  ⟨3072,some 406,[3174]⟩,
  ⟨3074,some 407,[3176]⟩,
  ⟨3076,some 408,[3178]⟩,
  ⟨3078,some 409,[3180]⟩,
  ⟨3080,some 410,[3182]⟩,
  ⟨3082,some 411,[3184]⟩,
  ⟨3084,some 412,[3186]⟩,
  ⟨3086,some 413,[3188]⟩,
  ⟨3088,some 414,[3190]⟩,
  ⟨3090,some 415,[3192]⟩,
  ⟨3092,some 416,[3194]⟩,
  ⟨3094,some 417,[3196]⟩,
  ⟨3096,some 418,[3198]⟩,
  ⟨3098,some 419,[3200]⟩,
  ⟨3100,none,[3202]⟩,
  ⟨3102,none,[3204]⟩,
  ⟨3104,none,[3206]⟩,
  ⟨3106,none,[3208]⟩,
  ⟨3108,none,[3210]⟩,
  ⟨3110,none,[3212]⟩,
  ⟨3112,none,[3214]⟩,
  ⟨3114,none,[3216]⟩,
  ⟨3116,none,[3218]⟩,
  ⟨3118,none,[3220]⟩,
  ⟨3120,none,[3222]⟩,
  ⟨3122,none,[3224]⟩,
  ⟨3124,none,[3226]⟩,
  ⟨3126,none,[3228]⟩,
  ⟨3128,none,[3230]⟩,
  ⟨3130,none,[3232]⟩,
  ⟨3132,none,[3234]⟩,
  ⟨3134,none,[3236]⟩,
  ⟨3136,none,[3238]⟩,
  ⟨3138,none,[3240]⟩,
  ⟨3140,none,[3242]⟩,
  ⟨3142,none,[3244]⟩,
  ⟨3144,none,[3246]⟩,
  ⟨3146,none,[3248]⟩,
  ⟨3148,none,[3250]⟩,
  ⟨3150,none,[3252]⟩,
  ⟨3152,none,[3254]⟩,
]

def step11Pieces : List (Fin poseCount) := [3156, 3155, 3159, 3158, 3161, 3163, 3165, 3168, 3167, 3170, 3172, 3174, 3176, 3178, 3180, 3182, 3184, 3186, 3188, 3190, 3192, 3194, 3196, 3198, 3200, 3202, 3204, 3206, 3208, 3210, 3212, 3214, 3216, 3218, 3220, 3222, 3224, 3226, 3228, 3230, 3232, 3234, 3236, 3238, 3240, 3242, 3244, 3246, 3248, 3250, 3252, 3254]
def step11Links : List (Fin 927) := [845, 844, 847, 846, 848, 849, 850, 852, 851, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]

def step11PairCheck (i : Fin 22) (j : Fin 61) : Prop :=
  (step11Sources i).PairCheck (step11Neighbors j)

instance (i : Fin 22) (j : Fin 61) :
    Decidable (step11PairCheck i j) :=
  inferInstanceAs (Decidable ((step11Sources i).PairCheck _))


end
end N12Compact.C898Cached.AllPairs
