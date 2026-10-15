import Compact.Bridge.CheckedCommonGroup
import Compact.HistoricalCommon.Bindings023
import Compact.HistoricalCommon.Bindings024
import Compact.HistoricalCommon.Bindings025
import Compact.HistoricalCommon.Bindings053
import Compact.HistoricalCommon.Bindings054
import Compact.HistoricalCommon.Bindings055
import Compact.HistoricalCommon.Keys

namespace N12Compact.HistoricalCommon.C701.Step09
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def sources : Fin 54 → Context dictionary :=
  ![context1748,context1759,context1765,context1776,context1787,context1788,context1789,context1790,context1791,context1698,context1739,context1740,context1741,context1742,context1743,context1744,context1745,context1746,context1747,context1749,context1750,context1751,context1752,context1753,context1754,context1755,context1756,context1757,context1758,context1760,context1761,context1762,context1763,context1764,context1766,context1767,context1768,context1769,context1770,context1771,context1772,context1773,context1774,context1775,context1777,context1778,context1779,context1780,context1781,context1782,context1783,context1784,context1785,context1786]

def neighbors : Fin 64 → Context dictionary :=
  ![context1699,context1700,context1701,context1702,context1703,context1704,context1705,context1706,context1707,context1708,context1709,context1710,context1711,context1712,context1713,context1714,context1715,context1716,context1717,context1718,context766,context768,context770,context772,context774,context776,context778,context780,context782,context784,context787,context789,context791,context793,context795,context797,context799,context801,context803,context805,context808,context810,context812,context814,context1719,context1720,context1721,context1722,context1723,context1724,context1725,context1726,context1727,context1728,context1729,context1730,context1731,context1732,context1733,context1734,context1735,context1736,context1737,context1738]


end
end N12Compact.HistoricalCommon.C701.Step09
