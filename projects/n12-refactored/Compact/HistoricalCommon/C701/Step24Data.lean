import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings013
import Compact.HistoricalCommon.Bindings014
import Compact.HistoricalCommon.Bindings032
import Compact.HistoricalCommon.Bindings033
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step24
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 59 → Context dictionary :=
  ![context1030,context1040,context1041,context1049,context1060,context1070,context1071,context1072,context1073,context425,context427,context429,context431,context433,context435,context437,context439,context441,context443,context445,context447,context449,context451,context453,context455,context457,context459,context461,context463,context465,context467,context469,context471,context1042,context1043,context1044,context1045,context1046,context1047,context1048,context1050,context1051,context1052,context1053,context1054,context1055,context1056,context1057,context1058,context1059,context1061,context1062,context1063,context1064,context1065,context1066,context1067,context1068,context1069]

def neighbors : Fin 9 → Context dictionary :=
  ![context1031,context1032,context1033,context1034,context1035,context1036,context1037,context1038,context1039]


end
end N12Compact.HistoricalCommon.C701.Step24
