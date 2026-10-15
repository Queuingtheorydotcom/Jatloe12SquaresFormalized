import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings021
import Compact.HistoricalCommon.Bindings022
import Compact.HistoricalCommon.Bindings023
import Compact.HistoricalCommon.Bindings050
import Compact.HistoricalCommon.Bindings051
import Compact.HistoricalCommon.Bindings052
import Compact.HistoricalCommon.Bindings053
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step08
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 38 → Context dictionary :=
  ![context1688,context1691,context1693,context1694,context1695,context1696,context1697,context1608,context1661,context1662,context1663,context1664,context1665,context1666,context1667,context1668,context1669,context1670,context1671,context1672,context1673,context1674,context1675,context1676,context1677,context1678,context1679,context1680,context1681,context1682,context1683,context1684,context1685,context1686,context1687,context1689,context1690,context1692]

def neighbors : Fin 64 → Context dictionary :=
  ![context1609,context692,context704,context716,context728,context740,context746,context748,context750,context752,context679,context681,context683,context1610,context1611,context1612,context1613,context1614,context1615,context1616,context1617,context1618,context1619,context1620,context1621,context1622,context1623,context1624,context1625,context1626,context1627,context1628,context1629,context1630,context1631,context1632,context1633,context1634,context1635,context1636,context1637,context1638,context1639,context1640,context1641,context1642,context1643,context1644,context1645,context1646,context1647,context1648,context1649,context1650,context1651,context1652,context1653,context1654,context1655,context1656,context1657,context1658,context1659,context1660]


end
end N12Compact.HistoricalCommon.C701.Step08
