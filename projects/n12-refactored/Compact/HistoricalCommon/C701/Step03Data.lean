import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings000
import Compact.HistoricalCommon.Bindings001
import Compact.HistoricalCommon.Bindings003
import Compact.HistoricalCommon.Bindings004
import Compact.HistoricalCommon.Bindings005
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step03
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 64 → Context dictionary :=
  ![context106,context117,context128,context139,context150,context161,context166,context167,context168,context169,context107,context108,context109,context110,context111,context112,context113,context114,context115,context116,context118,context119,context120,context121,context122,context123,context124,context125,context126,context127,context129,context130,context131,context132,context133,context134,context135,context136,context137,context138,context140,context141,context142,context143,context144,context145,context146,context147,context148,context149,context151,context152,context153,context154,context155,context156,context157,context158,context159,context160,context162,context163,context164,context165]

def neighbors : Fin 59 → Context dictionary :=
  ![context1,context2,context3,context4,context5,context6,context7,context8,context9,context10,context11,context12,context13,context14,context15,context16,context17,context18,context19,context20,context21,context22,context23,context24,context25,context26,context27,context28,context29,context30,context31,context32,context33,context34,context35,context36,context37,context38,context39,context40,context41,context42,context43,context44,context45,context46,context47,context48,context49,context50,context51,context52,context53,context54,context55,context56,context57,context58,context59]


end
end N12Compact.HistoricalCommon.C701.Step03
