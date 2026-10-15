import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings035
import Compact.HistoricalCommon.Bindings036
import Compact.HistoricalCommon.Bindings039
import Compact.HistoricalCommon.Bindings040
import Compact.HistoricalCommon.Bindings041
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step29
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 64 → Context dictionary :=
  ![context1258,context1269,context1280,context1291,context1302,context1313,context1318,context1319,context1320,context1321,context1259,context1260,context1261,context1262,context1263,context1264,context1265,context1266,context1267,context1268,context1270,context1271,context1272,context1273,context1274,context1275,context1276,context1277,context1278,context1279,context1281,context1282,context1283,context1284,context1285,context1286,context1287,context1288,context1289,context1290,context1292,context1293,context1294,context1295,context1296,context1297,context1298,context1299,context1300,context1301,context1303,context1304,context1305,context1306,context1307,context1308,context1309,context1310,context1311,context1312,context1314,context1315,context1316,context1317]

def neighbors : Fin 7 → Context dictionary :=
  ![context1148,context1149,context1150,context1151,context1152,context1153,context1154]


end
end N12Compact.HistoricalCommon.C701.Step29
