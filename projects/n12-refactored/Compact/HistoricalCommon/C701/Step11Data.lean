import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings008
import Compact.HistoricalCommon.Bindings009
import Compact.HistoricalCommon.Bindings010
import Compact.HistoricalCommon.Bindings011
import Compact.HistoricalCommon.Bindings012
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step11
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 63 → Context dictionary :=
  ![context274,context362,context373,context384,context395,context406,context410,context411,context412,context413,context352,context353,context354,context355,context356,context357,context358,context359,context360,context361,context363,context364,context365,context366,context367,context368,context369,context370,context371,context372,context374,context375,context376,context377,context378,context379,context380,context381,context382,context383,context385,context386,context387,context388,context389,context390,context391,context392,context393,context394,context396,context397,context398,context399,context400,context401,context402,context403,context404,context405,context407,context408,context409]

def neighbors : Fin 45 → Context dictionary :=
  ![context275,context276,context277,context278,context279,context280,context282,context284,context286,context287,context288,context289,context290,context291,context293,context295,context297,context299,context301,context303,context304,context305,context307,context309,context311,context313,context315,context317,context319,context321,context323,context325,context327,context329,context331,context333,context335,context337,context339,context341,context343,context345,context347,context349,context351]


end
end N12Compact.HistoricalCommon.C701.Step11
