import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings041
import Compact.HistoricalCommon.Bindings042
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step30
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 31 → Context dictionary :=
  ![context1322,context1343,context1354,context1356,context1357,context1358,context1359,context1360,context1361,context1362,context1333,context1334,context1335,context1336,context1337,context1338,context1339,context1340,context1341,context1342,context1344,context1345,context1346,context1347,context1348,context1349,context1350,context1351,context1352,context1353,context1355]

def neighbors : Fin 10 → Context dictionary :=
  ![context1323,context1324,context1325,context1326,context1327,context1328,context1329,context1330,context1331,context1332]


end
end N12Compact.HistoricalCommon.C701.Step30
