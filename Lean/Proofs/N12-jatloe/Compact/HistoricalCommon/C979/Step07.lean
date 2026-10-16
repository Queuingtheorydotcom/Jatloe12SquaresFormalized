import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step07
import Compact.HistoricalCommon.C979.Step07Groups00
import Compact.HistoricalCommon.C979.Step07Groups01
import Compact.HistoricalCommon.C979.Step07Groups02
import Compact.HistoricalCommon.C979.Step07Groups03
import Compact.HistoricalCommon.C979.Step07Groups04
import Compact.HistoricalCommon.C979.Step07Groups05
import Compact.HistoricalCommon.C979.Step07Groups06
import Compact.HistoricalCommon.C979.Step07Groups07
import Compact.HistoricalCommon.C979.Step07Groups08
import Compact.HistoricalCommon.C979.Step07Groups09
import Compact.HistoricalCommon.C979.Step07Groups10

namespace N12Compact.HistoricalCommon.C979.Step07
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 64 (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 16 (.neighborCut 8 .leaf .leaf) (.neighborCut 8 .leaf .leaf))) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 8 .leaf .leaf))) (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf))) (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf))))))))) (.neighborCut 16 (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf .leaf)))) (.neighborCut 16 .leaf (.neighborCut 32 .leaf (.sourceCut 16 (.neighborCut 32 .leaf .leaf) (.sourceCut 16 (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 8 .leaf .leaf) .leaf)) (.sourceCut 16 (.neighborCut 32 .leaf (.neighborCut 16 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 8 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,128,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context12930_header,context12978_header,context12989_header,context13000_header,context13011_header,context13022_header,context13033_header,context13044_header,context13055_header,context13066_header,context12950_header,context12961_header,context12970_header,context12971_header,context12972_header,context12973_header,context12974_header,context12975_header,context12976_header,context12977_header,context12979_header,context12980_header,context12981_header,context12982_header,context12983_header,context12984_header,context12985_header,context12986_header,context12987_header,context12988_header,context12990_header,context12991_header,context12992_header,context12993_header,context12994_header,context12995_header,context12996_header,context12997_header,context12998_header,context12999_header,context13001_header,context13002_header,context13003_header,context13004_header,context13005_header,context13006_header,context13007_header,context13008_header,context13009_header,context13010_header,context13012_header,context13013_header,context13014_header,context13015_header,context13016_header,context13017_header,context13018_header,context13019_header,context13020_header,context13021_header,context13023_header,context13024_header,context13025_header,context13026_header,context13027_header,context13028_header,context13029_header,context13030_header,context13031_header,context13032_header,context13034_header,context13035_header,context13036_header,context13037_header,context13038_header,context13039_header,context13040_header,context13041_header,context13042_header,context13043_header,context13045_header,context13046_header,context13047_header,context13048_header,context13049_header,context13050_header,context13051_header,context13052_header,context13053_header,context13054_header,context13056_header,context13057_header,context13058_header,context13059_header,context13060_header,context13061_header,context13062_header,context13063_header,context13064_header,context13065_header,context12940_header,context12941_header,context12942_header,context12943_header,context12944_header,context12945_header,context12946_header,context12947_header,context12948_header,context12949_header,context12951_header,context12952_header,context12953_header,context12954_header,context12955_header,context12956_header,context12957_header,context12958_header,context12959_header,context12960_header,context12962_header,context12963_header,context12964_header,context12965_header,context12966_header,context12967_header,context12968_header,context12969_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1939,some (fanBlockRows 1583)),(1940,some (fanBlockRows 1622)),(1941,some (fanBlockRows 1633)),(1942,some (fanBlockRows 1644)),(1943,some (fanBlockRows 1655)),(1944,some (fanBlockRows 1666)),(1945,some (fanBlockRows 1677)),(1946,some (fanBlockRows 1686)),(1947,some (fanBlockRows 1687)),(1948,some (fanBlockRows 1695)),(1949,some (fanBlockRows 1594)),(1950,some (fanBlockRows 1605)),(1951,some (fanBlockRows 1614)),(1952,some (fanBlockRows 1615)),(1953,some (fanBlockRows 1616)),(1954,some (fanBlockRows 1617)),(1955,some (fanBlockRows 1618)),(1956,some (fanBlockRows 1619)),(1957,some (fanBlockRows 1620)),(1958,some (fanBlockRows 1621)),(1959,some (fanBlockRows 1623)),(1960,some (fanBlockRows 1624)),(1961,some (fanBlockRows 1625)),(1962,some (fanBlockRows 1626)),(1963,some (fanBlockRows 1627)),(1964,some (fanBlockRows 1628)),(1965,some (fanBlockRows 1629)),(1966,some (fanBlockRows 1630)),(1967,some (fanBlockRows 1631)),(1968,some (fanBlockRows 1632)),(1969,some (fanBlockRows 1634)),(1970,some (fanBlockRows 1635)),(1971,some (fanBlockRows 1636)),(1972,some (fanBlockRows 1637)),(1973,some (fanBlockRows 1638)),(1974,some (fanBlockRows 1639)),(1975,some (fanBlockRows 1640)),(1976,some (fanBlockRows 1641)),(1977,some (fanBlockRows 1642)),(1978,some (fanBlockRows 1643)),(1979,some (fanBlockRows 1645)),(1980,some (fanBlockRows 1646)),(1981,some (fanBlockRows 1647)),(1982,some (fanBlockRows 1648)),(1983,some (fanBlockRows 1649)),(1984,some (fanBlockRows 1650)),(1985,some (fanBlockRows 1651)),(1986,some (fanBlockRows 1652)),(1987,some (fanBlockRows 1653)),(1988,some (fanBlockRows 1654)),(1989,some (fanBlockRows 1656)),(1990,some (fanBlockRows 1657)),(1991,some (fanBlockRows 1658)),(1992,some (fanBlockRows 1659)),(1993,some (fanBlockRows 1660)),(1994,some (fanBlockRows 1661)),(1995,some (fanBlockRows 1662)),(1996,some (fanBlockRows 1663)),(1997,some (fanBlockRows 1664)),(1998,some (fanBlockRows 1665)),(1999,some (fanBlockRows 1667)),(2000,some (fanBlockRows 1668)),(2001,some (fanBlockRows 1669)),(2002,some (fanBlockRows 1670)),(2003,some (fanBlockRows 1671)),(2004,some (fanBlockRows 1672)),(2005,some (fanBlockRows 1673)),(2006,some (fanBlockRows 1674)),(2007,some (fanBlockRows 1675)),(2008,some (fanBlockRows 1676)),(2009,some (fanBlockRows 1678)),(2010,some (fanBlockRows 1679)),(2011,some (fanBlockRows 1680)),(2012,some (fanBlockRows 1681)),(2013,some (fanBlockRows 1682)),(2014,some (fanBlockRows 1683)),(2015,some (fanBlockRows 1684)),(2016,some (fanBlockRows 1685)),(2017,some (fanBlockRows 59)),(2018,some (fanBlockRows 59)),(2019,some (fanBlockRows 59)),(2020,some (fanBlockRows 59)),(2021,some (fanBlockRows 59)),(2022,some (fanBlockRows 59)),(2023,some (fanBlockRows 59)),(2024,some (fanBlockRows 59)),(2025,some (fanBlockRows 59)),(2026,some (fanBlockRows 59)),(2027,some (fanBlockRows 59)),(2028,some (fanBlockRows 59)),(2029,some (fanBlockRows 59)),(2030,some (fanBlockRows 59)),(2031,some (fanBlockRows 59)),(2032,some (fanBlockRows 1688)),(2033,some (fanBlockRows 1689)),(2034,some (fanBlockRows 1690)),(2035,some (fanBlockRows 1691)),(2036,some (fanBlockRows 1692)),(2037,some (fanBlockRows 1693)),(2038,some (fanBlockRows 1694)),(2039,some (fanBlockRows 1584)),(2040,some (fanBlockRows 1585)),(2041,some (fanBlockRows 1586)),(2042,some (fanBlockRows 1587)),(2043,some (fanBlockRows 1588)),(2044,some (fanBlockRows 1589)),(2045,some (fanBlockRows 1590)),(2046,some (fanBlockRows 1591)),(2047,some (fanBlockRows 1592)),(2048,some (fanBlockRows 1593)),(2049,some (fanBlockRows 1595)),(2050,some (fanBlockRows 1596)),(2051,some (fanBlockRows 1597)),(2052,some (fanBlockRows 1598)),(2053,some (fanBlockRows 1599)),(2054,some (fanBlockRows 1600)),(2055,some (fanBlockRows 1601)),(2056,some (fanBlockRows 1602)),(2057,some (fanBlockRows 1603)),(2058,some (fanBlockRows 1604)),(2059,some (fanBlockRows 1606)),(2060,some (fanBlockRows 1607)),(2061,some (fanBlockRows 1608)),(2062,some (fanBlockRows 1609)),(2063,some (fanBlockRows 1610)),(2064,some (fanBlockRows 1611)),(2065,some (fanBlockRows 1612)),(2066,some (fanBlockRows 1613))]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step07.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain1_1Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step07.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step07.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain1_1Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain1_1Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step07
