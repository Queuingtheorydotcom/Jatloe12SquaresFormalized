import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings017
import Compact.HistoricalCommon.Bindings043
import Compact.HistoricalCommon.Bindings046
import Compact.HistoricalCommon.Bindings047
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step05
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 52 → Context dictionary :=
  ![context1520,context1521,context1522,context1523,context1479,context1480,context1481,context1482,context1483,context1484,context1485,context1486,context1487,context1488,context1489,context1490,context1387,context1389,context1391,context1393,context1395,context1397,context1399,context1491,context1492,context1493,context1494,context1495,context1496,context1497,context1498,context1499,context1500,context1501,context1502,context1503,context1504,context1505,context1506,context1507,context1508,context1509,context1510,context1511,context1512,context1513,context1514,context1515,context1516,context1517,context1518,context1519]

def neighbors : Fin 25 → Context dictionary :=
  ![context544,context545,context546,context547,context548,context549,context550,context551,context552,context553,context554,context555,context556,context557,context558,context559,context560,context561,context562,context563,context564,context565,context566,context567,context568]


end
end N12Compact.HistoricalCommon.C701.Step05
