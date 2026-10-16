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

checked_common_fan context2016 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1994,fanBlockRows 763⟩ using [109419,190,14361,14362,14363,14364]
checked_common_fan context2017 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1995,fanBlockRows 764⟩ using [109420,14366,14367,14368,14369,14370]
checked_common_fan context2018 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1996,fanBlockRows 765⟩ using [109421,196,14372,14373,14374,14375]
checked_common_fan context2019 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1997,fanBlockRows 766⟩ using [109422,85471,14377,14378,14379,14380,14381]
checked_common_fan context2020 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1998,fanBlockRows 767⟩ using [109423,202,14383,14384,14385,14386]
checked_common_fan context2021 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨1999,fanBlockRows 768⟩ using [109424,85475,14388,14389,14390,14391,14392]
checked_common_fan context2022 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2000,fanBlockRows 769⟩ using [109425,208,14394,14395,14396,14397]
checked_common_fan context2023 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2001,fanBlockRows 770⟩ using [109426,85479,14399,14400,14401,14402,14403]
checked_common_fan context2024 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2002,fanBlockRows 771⟩ using [109427,214,14405,14406,14407,14408]
checked_common_fan context2025 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2003,fanBlockRows 772⟩ using [109428,85483,14410,14411,14412,14413,14414]
checked_common_fan context2026 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2004,fanBlockRows 773⟩ using [109429,85486,220,14416,14417,14418,14419]
checked_common_fan context2027 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2005,fanBlockRows 774⟩ using [109430,85489,14421,14422,14423,14424,14425]
checked_common_fan context2028 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2006,fanBlockRows 775⟩ using [109431,85492,226,14427,14428,14429,14430]
checked_common_fan context2029 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2007,fanBlockRows 776⟩ using [109432,85495,14432,14433,14434,14435,14436]
checked_common_fan context2030 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2008,fanBlockRows 777⟩ using [109433,232,14438,14439,14440,14441]
checked_common_fan context2031 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2009,fanBlockRows 778⟩ using [109434,85499,14443,14444,14445,14446,14447]
checked_common_fan context2032 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2010,fanBlockRows 779⟩ using [109435,85502,238,14449,14450,14451,14452]
checked_common_fan context2033 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2011,fanBlockRows 780⟩ using [109436,85505,14454,14455,14456,14457,14458]
checked_common_fan context2034 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2012,fanBlockRows 781⟩ using [109437,85508,244,14460,14461,14462,14463]
checked_common_fan context2035 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2013,fanBlockRows 782⟩ using [109438,85511,14465,14466,14467,14468,14469]
checked_common_fan context2036 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2014,fanBlockRows 783⟩ using [109439,85514,250,14471,14472,14473,14474]
checked_common_fan context2037 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2015,fanBlockRows 784⟩ using [109440,85517,14476,14477,14478,14479,14480]
checked_common_fan context2038 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2016,fanBlockRows 785⟩ using [109441,85520,256,14482,14483,14484,14485]
checked_common_fan context2039 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2017,fanBlockRows 786⟩ using [109442,85523,14487,14488,14489,14490,14491]
checked_common_fan context2040 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2018,fanBlockRows 787⟩ using [109443,85526,262,14493,14494]
checked_common_fan context2041 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2019,fanBlockRows 788⟩ using [109444,14498,14499,14500]
checked_common_fan context2042 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2020,fanBlockRows 789⟩ using [109445,268,14504,14505]
checked_common_fan context2043 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2021,fanBlockRows 790⟩ using [109446,14509,14510,14511,14512,14513,14514]
checked_common_fan context2044 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2022,fanBlockRows 791⟩ using [109447,14516,14517,14518,14519,14520]
checked_common_fan context2045 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2023,fanBlockRows 792⟩ using [109448,14523,14524,14525,14526,14527]
checked_common_fan context2046 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2024,fanBlockRows 793⟩ using [109449,14529,14530,14531,14532,14533]
checked_common_fan context2047 (dictionary,N12Compact.HistoricalFans.C701_713_717_973_978_979.directions) := ⟨2025,fanBlockRows 794⟩ using [109450,14536,14537,14538,14539,14540]

end
end N12Compact.HistoricalCommon
