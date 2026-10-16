import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings261
import Compact.HistoricalCommon.Bindings262
import Compact.HistoricalCommon.Bindings263
import Compact.HistoricalCommon.Bindings264
import Compact.HistoricalCommon.Bindings265
import Compact.HistoricalCommon.Bindings266
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C973.Step06
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 64 → Context dictionary :=
  ![context8379,context8464,context8475,context8486,context8497,context8508,context8513,context8514,context8515,context8516,context8454,context8455,context8456,context8457,context8458,context8459,context8460,context8461,context8462,context8463,context8465,context8466,context8467,context8468,context8469,context8470,context8471,context8472,context8473,context8474,context8476,context8477,context8478,context8479,context8480,context8481,context8482,context8483,context8484,context8485,context8487,context8488,context8489,context8490,context8491,context8492,context8493,context8494,context8495,context8496,context8498,context8499,context8500,context8501,context8502,context8503,context8504,context8505,context8506,context8507,context8509,context8510,context8511,context8512]

def neighbors : Fin 64 → Context dictionary :=
  ![context8380,context8381,context8382,context8383,context8384,context8385,context8386,context8387,context8388,context8389,context8390,context8391,context8392,context8393,context8394,context8395,context8396,context8397,context8398,context8399,context8400,context8401,context8403,context8405,context8407,context8409,context8411,context8413,context8415,context8417,context8419,context8421,context8422,context8423,context8424,context8425,context8426,context8427,context8428,context8429,context8430,context8431,context8432,context8433,context8434,context8435,context8436,context8437,context8438,context8439,context8440,context8441,context8442,context8443,context8444,context8445,context8446,context8447,context8448,context8449,context8450,context8451,context8452,context8453]


end
end N12Compact.HistoricalCommon.C973.Step06
