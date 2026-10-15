import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step00
import Compact.HistoricalCommon.C717.Step00Groups00
import Compact.HistoricalCommon.C717.Step00Groups01
import Compact.HistoricalCommon.C717.Step00Groups02
import Compact.HistoricalCommon.C717.Step00Groups03
import Compact.HistoricalCommon.C717.Step00Groups04
import Compact.HistoricalCommon.C717.Step00Groups05
import Compact.HistoricalCommon.C717.Step00Groups06
import Compact.HistoricalCommon.C717.Step00Groups07
import Compact.HistoricalCommon.C717.Step00Groups08
import Compact.HistoricalCommon.C717.Step00Groups09
import Compact.HistoricalCommon.C717.Step00Groups10
import Compact.HistoricalCommon.C717.Step00Groups11
import Compact.HistoricalCommon.C717.Step00Groups12

namespace N12Compact.HistoricalCommon.C717.Step00
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44,group45,group46,group47,group48,group49,group50]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope,group45_scope,group46_scope,group47_scope,group48_scope,group49_scope,group50_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 54 (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 14 (.neighborCut 8 .leaf .leaf) (.sourceCut 13 .leaf .leaf))) (.neighborCut 16 .leaf (.sourceCut 27 (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 16 .leaf (.neighborCut 16 .leaf .leaf)) (.neighborCut 16 (.sourceCut 7 .leaf .leaf) (.neighborCut 16 .leaf .leaf))))) (.neighborCut 16 (.sourceCut 13 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 16 .leaf (.neighborCut 8 .leaf .leaf)) .leaf)))))))) (.sourceCut 27 (.neighborCut 32 .leaf (.neighborCut 32 .leaf (.neighborCut 16 (.sourceCut 13 .leaf .leaf) (.neighborCut 16 (.sourceCut 13 .leaf (.neighborCut 8 .leaf .leaf)) (.neighborCut 8 .leaf (.neighborCut 8 .leaf .leaf)))))) (.neighborCut 16 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 16 .leaf (.neighborCut 16 (.sourceCut 13 .leaf .leaf) (.neighborCut 16 (.sourceCut 6 .leaf (.sourceCut 7 .leaf .leaf)) (.neighborCut 32 .leaf (.neighborCut 16 .leaf (.sourceCut 13 (.neighborCut 8 .leaf .leaf) .leaf)))))))))

theorem partition_checked : partition.Check ⟨0,108,0,128⟩ scopes := by decide +kernel

theorem covered (i : Fin 108) (j : Fin 128) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 108) (j : Fin 128) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context3672_header,context3831_header,context3842_header,context3853_header,context3857_header,context3858_header,context3866_header,context3877_header,context3888_header,context3899_header,context3803_header,context3814_header,context3823_header,context3824_header,context3825_header,context3826_header,context3827_header,context3828_header,context3829_header,context3830_header,context3832_header,context3833_header,context3834_header,context3835_header,context3836_header,context3837_header,context3838_header,context3839_header,context3840_header,context3841_header,context3843_header,context3844_header,context3845_header,context3846_header,context3847_header,context3848_header,context3849_header,context3850_header,context3851_header,context3852_header,context3854_header,context3855_header,context3856_header,context3859_header,context3860_header,context3861_header,context3862_header,context3863_header,context3864_header,context3865_header,context3867_header,context3868_header,context3869_header,context3870_header,context3871_header,context3872_header,context3873_header,context3874_header,context3875_header,context3876_header,context3878_header,context3879_header,context3880_header,context3881_header,context3882_header,context3883_header,context3884_header,context3885_header,context3886_header,context3887_header,context3889_header,context3890_header,context3891_header,context3892_header,context3893_header,context3894_header,context3895_header,context3896_header,context3897_header,context3898_header,context3793_header,context3794_header,context3795_header,context3796_header,context3797_header,context3798_header,context3799_header,context3800_header,context3801_header,context3802_header,context3804_header,context3805_header,context3806_header,context3807_header,context3808_header,context3809_header,context3810_header,context3811_header,context3812_header,context3813_header,context3815_header,context3816_header,context3817_header,context3818_header,context3819_header,context3820_header,context3821_header,context3822_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 108).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1939,some (fanBlockRows 1360)),(1940,some (fanBlockRows 1399)),(1941,some (fanBlockRows 1410)),(1942,some (fanBlockRows 1421)),(1943,some (fanBlockRows 1425)),(1944,some (fanBlockRows 1426)),(1945,some (fanBlockRows 1434)),(1946,some (fanBlockRows 1445)),(1947,some (fanBlockRows 1456)),(1948,some (fanBlockRows 1467)),(1949,some (fanBlockRows 1371)),(1950,some (fanBlockRows 1382)),(1951,some (fanBlockRows 1391)),(1952,some (fanBlockRows 1392)),(1953,some (fanBlockRows 1393)),(1954,some (fanBlockRows 1394)),(1955,some (fanBlockRows 1395)),(1956,some (fanBlockRows 1396)),(1957,some (fanBlockRows 1397)),(1958,some (fanBlockRows 1398)),(1959,some (fanBlockRows 1400)),(1960,some (fanBlockRows 1401)),(1961,some (fanBlockRows 1402)),(1962,some (fanBlockRows 1403)),(1963,some (fanBlockRows 1404)),(1964,some (fanBlockRows 1405)),(1965,some (fanBlockRows 1406)),(1966,some (fanBlockRows 1407)),(1967,some (fanBlockRows 1408)),(1968,some (fanBlockRows 1409)),(1969,some (fanBlockRows 1411)),(1970,some (fanBlockRows 1412)),(1971,some (fanBlockRows 1413)),(1972,some (fanBlockRows 1414)),(1973,some (fanBlockRows 1415)),(1974,some (fanBlockRows 1416)),(1975,some (fanBlockRows 1417)),(1976,some (fanBlockRows 1418)),(1977,some (fanBlockRows 1419)),(1978,some (fanBlockRows 1420)),(1979,some (fanBlockRows 1422)),(1980,some (fanBlockRows 1423)),(1981,some (fanBlockRows 1424)),(1982,none),(1983,none),(1984,none),(1985,none),(1986,none),(1987,none),(1988,none),(1989,none),(1990,none),(1991,none),(1992,none),(1993,none),(1994,none),(1995,none),(1996,none),(1997,none),(1998,none),(1999,none),(2000,none),(2001,none),(2002,some (fanBlockRows 1427)),(2003,some (fanBlockRows 1428)),(2004,some (fanBlockRows 1429)),(2005,some (fanBlockRows 1430)),(2006,some (fanBlockRows 1431)),(2007,some (fanBlockRows 1432)),(2008,some (fanBlockRows 1433)),(2009,some (fanBlockRows 1435)),(2010,some (fanBlockRows 1436)),(2011,some (fanBlockRows 1437)),(2012,some (fanBlockRows 1438)),(2013,some (fanBlockRows 1439)),(2014,some (fanBlockRows 1440)),(2015,some (fanBlockRows 1441)),(2016,some (fanBlockRows 1442)),(2017,some (fanBlockRows 1443)),(2018,some (fanBlockRows 1444)),(2019,some (fanBlockRows 1446)),(2020,some (fanBlockRows 1447)),(2021,some (fanBlockRows 1448)),(2022,some (fanBlockRows 1449)),(2023,some (fanBlockRows 1450)),(2024,some (fanBlockRows 1451)),(2025,some (fanBlockRows 1452)),(2026,some (fanBlockRows 1453)),(2027,some (fanBlockRows 1454)),(2028,some (fanBlockRows 1455)),(2029,some (fanBlockRows 1457)),(2030,some (fanBlockRows 1458)),(2031,some (fanBlockRows 1459)),(2032,some (fanBlockRows 1460)),(2033,some (fanBlockRows 1461)),(2034,some (fanBlockRows 1462)),(2035,some (fanBlockRows 1463)),(2036,some (fanBlockRows 1464)),(2037,some (fanBlockRows 1465)),(2038,some (fanBlockRows 1466)),(2039,some (fanBlockRows 1361)),(2040,some (fanBlockRows 1362)),(2041,some (fanBlockRows 1363)),(2042,some (fanBlockRows 1364)),(2043,some (fanBlockRows 1365)),(2044,some (fanBlockRows 1366)),(2045,some (fanBlockRows 1367)),(2046,some (fanBlockRows 1368)),(2047,some (fanBlockRows 1369)),(2048,some (fanBlockRows 1370)),(2049,some (fanBlockRows 1372)),(2050,some (fanBlockRows 1373)),(2051,some (fanBlockRows 1374)),(2052,some (fanBlockRows 1375)),(2053,some (fanBlockRows 1376)),(2054,some (fanBlockRows 1377)),(2055,some (fanBlockRows 1378)),(2056,some (fanBlockRows 1379)),(2057,some (fanBlockRows 1380)),(2058,some (fanBlockRows 1381)),(2059,some (fanBlockRows 1383)),(2060,some (fanBlockRows 1384)),(2061,some (fanBlockRows 1385)),(2062,some (fanBlockRows 1386)),(2063,some (fanBlockRows 1387)),(2064,some (fanBlockRows 1388)),(2065,some (fanBlockRows 1389)),(2066,some (fanBlockRows 1390))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step00.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 128).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain1_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step00.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step00.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain1_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain1_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step00
