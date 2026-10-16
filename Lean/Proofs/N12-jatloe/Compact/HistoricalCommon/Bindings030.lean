import Compact.Bridge.CheckedCommonContext
import Compact.Bridge.CheckedCommonFanCommand
import Compact.Cases.C713.SharedDictionary
import Compact.HistoricalData.SharedFanBlocks
import Compact.HistoricalFans.C701_713_717_973_978_979.Directions

namespace N12Compact.HistoricalCommon
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option maxRecDepth 10000
set_option linter.unnecessarySeqFocus false
noncomputable section

checked_common_fan context960 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨645,fanBlockRows 390⟩ using [109046,4958,4959,4960,4961,4962,4963]
checked_common_fan context961 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨646,fanBlockRows 391⟩ using [4971,109047,4966,4967,4968,4969,4970]
checked_common_fan context962 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨647,fanBlockRows 59⟩ using [4979,4972,4973,4974,4975,4976,4977,4978]
checked_common_fan context963 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨648,fanBlockRows 59⟩ using [4987,4980,4981,4982,4983,4984,4985,4986]
checked_common_fan context964 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨649,fanBlockRows 59⟩ using [4995,4988,4989,4990,4991,4992,4993,4994]
checked_common_fan context965 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨650,fanBlockRows 59⟩ using [5003,4996,4997,4998,4999,5000,5001,5002]
checked_common_fan context966 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1038,fanBlockRows 392⟩ using [7332,7326,7327,7328,109048,7331]
checked_common_fan context967 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1048,fanBlockRows 59⟩ using [7396,7391,7392,7393,1531,7394,7395]
checked_common_fan context968 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1049,fanBlockRows 59⟩ using [7402,7397,7398,7399,1540,7400,7401]
checked_common_fan context969 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1050,fanBlockRows 393⟩ using [7408,7403,7404,7405,1549,109049,7407]
checked_common_fan context970 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1051,fanBlockRows 394⟩ using [7414,7409,7410,7411,1557,109050,7413]
checked_common_fan context971 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1052,fanBlockRows 395⟩ using [7420,7415,7416,7417,1565,109051,7419]
checked_common_fan context972 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1053,fanBlockRows 396⟩ using [7425,7421,7422,1573,109052,7424]
checked_common_fan context973 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1054,fanBlockRows 397⟩ using [7430,7426,7427,1581,109053,7429]
checked_common_fan context974 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1055,fanBlockRows 398⟩ using [7435,7431,7432,1589,109054,7434]
checked_common_fan context975 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1056,fanBlockRows 399⟩ using [7440,7436,7437,1597,109055,7439]
checked_common_fan context976 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1057,fanBlockRows 400⟩ using [7445,7441,7442,1605,109056,7444]
checked_common_fan context977 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1039,fanBlockRows 401⟩ using [7339,7333,7334,7335,109057,7337,7338]
checked_common_fan context978 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1058,fanBlockRows 59⟩ using [7450,7446,7447,1613,7448,7449]
checked_common_fan context979 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1059,fanBlockRows 59⟩ using [7455,7451,7452,1621,7453,7454]
checked_common_fan context980 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1060,fanBlockRows 59⟩ using [7460,7456,7457,1628,7458,7459]
checked_common_fan context981 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1061,fanBlockRows 59⟩ using [7465,7461,7462,1634,7463,7464]
checked_common_fan context982 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1062,fanBlockRows 59⟩ using [7470,7466,7467,1640,7468,7469]
checked_common_fan context983 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1063,fanBlockRows 59⟩ using [7475,7471,7472,1646,7473,7474]
checked_common_fan context984 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1064,fanBlockRows 59⟩ using [7480,7476,7477,5721,7478,7479]
checked_common_fan context985 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1065,fanBlockRows 59⟩ using [7485,7481,7482,5726,7483,7484]
checked_common_fan context986 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1066,fanBlockRows 59⟩ using [7490,7486,7487,5731,7488,7489]
checked_common_fan context987 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1067,fanBlockRows 59⟩ using [7495,7491,7492,5736,7493,7494]
checked_common_fan context988 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1040,fanBlockRows 402⟩ using [7346,7340,7341,7342,109058,7345]
checked_common_fan context989 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1068,fanBlockRows 59⟩ using [7500,7496,7497,5741,7498,7499]
checked_common_fan context990 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1069,fanBlockRows 59⟩ using [7505,7501,7502,1652,7503,7504]
checked_common_fan context991 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1070,fanBlockRows 59⟩ using [7510,7506,7507,1659,7508,7509]

end
end N12Compact.HistoricalCommon
