import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step00
import Compact.HistoricalCommon.C713.Step00Groups00
import Compact.HistoricalCommon.C713.Step00Groups01
import Compact.HistoricalCommon.C713.Step00Groups02
import Compact.HistoricalCommon.C713.Step00Groups03
import Compact.HistoricalCommon.C713.Step00Groups04
import Compact.HistoricalCommon.C713.Step00Groups05
import Compact.HistoricalCommon.C713.Step00Groups06
import Compact.HistoricalCommon.C713.Step00Groups07

namespace N12Compact.HistoricalCommon.C713.Step00
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 54 (.neighborCut 28 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 15 .leaf (.neighborCut 28 .leaf (.sourceCut 27 (.neighborCut 14 .leaf (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf))) (.sourceCut 13 (.neighborCut 14 .leaf .leaf) (.neighborCut 14 .leaf (.sourceCut 7 .leaf .leaf))))))))) (.neighborCut 14 (.sourceCut 27 .leaf (.sourceCut 14 .leaf (.neighborCut 7 .leaf .leaf))) (.neighborCut 14 (.sourceCut 13 .leaf (.sourceCut 7 .leaf (.sourceCut 7 .leaf .leaf))) (.neighborCut 29 .leaf (.neighborCut 28 .leaf (.sourceCut 27 (.neighborCut 14 (.sourceCut 13 .leaf (.sourceCut 7 .leaf .leaf)) .leaf) (.neighborCut 14 (.sourceCut 14 .leaf (.sourceCut 7 .leaf .leaf)) .leaf)))))))

theorem partition_checked : partition.Check ⟨0,109,0,114⟩ scopes := by decide +kernel

theorem covered (i : Fin 109) (j : Fin 114) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 109) (j : Fin 114) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context2051_header,context2062_header,context1964_header,context1972_header,context1973_header,context1974_header,context1975_header,context1976_header,context1977_header,context1978_header,context1979_header,context1980_header,context1981_header,context1982_header,context1983_header,context1984_header,context1985_header,context1986_header,context1987_header,context1988_header,context1989_header,context1990_header,context1991_header,context1992_header,context1993_header,context1994_header,context1995_header,context1996_header,context1997_header,context1998_header,context1999_header,context2000_header,context2001_header,context2002_header,context2003_header,context2004_header,context2005_header,context2006_header,context2007_header,context2008_header,context2009_header,context2010_header,context2011_header,context2012_header,context2013_header,context2014_header,context2015_header,context2016_header,context2017_header,context2018_header,context2019_header,context2020_header,context2021_header,context2022_header,context2023_header,context2024_header,context2025_header,context2026_header,context2027_header,context2028_header,context2029_header,context2030_header,context2031_header,context2032_header,context2033_header,context2034_header,context2035_header,context2036_header,context2037_header,context2038_header,context2039_header,context2040_header,context2041_header,context2042_header,context2043_header,context2044_header,context2045_header,context2046_header,context2047_header,context2048_header,context2049_header,context2050_header,context2052_header,context2053_header,context2054_header,context2055_header,context2056_header,context2057_header,context2058_header,context2059_header,context2060_header,context2061_header,context1792_header,context1955_header,context1956_header,context1957_header,context1958_header,context1959_header,context1960_header,context1961_header,context1962_header,context1963_header,context1965_header,context1966_header,context1967_header,context1968_header,context1969_header,context1970_header,context1971_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 109).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1939,none),(1940,none),(1941,none),(1942,none),(1943,none),(1944,none),(1945,none),(1946,none),(1947,some (fanBlockRows 798)),(1948,some (fanBlockRows 809)),(1949,some (fanBlockRows 711)),(1950,some (fanBlockRows 719)),(1951,some (fanBlockRows 720)),(1952,some (fanBlockRows 721)),(1953,some (fanBlockRows 722)),(1954,some (fanBlockRows 723)),(1955,some (fanBlockRows 724)),(1956,some (fanBlockRows 725)),(1957,some (fanBlockRows 726)),(1958,some (fanBlockRows 727)),(1959,some (fanBlockRows 728)),(1960,some (fanBlockRows 729)),(1961,some (fanBlockRows 730)),(1962,some (fanBlockRows 731)),(1963,some (fanBlockRows 732)),(1964,some (fanBlockRows 733)),(1965,some (fanBlockRows 734)),(1966,some (fanBlockRows 735)),(1967,some (fanBlockRows 736)),(1968,some (fanBlockRows 737)),(1969,some (fanBlockRows 738)),(1970,some (fanBlockRows 739)),(1971,some (fanBlockRows 740)),(1972,some (fanBlockRows 741)),(1973,some (fanBlockRows 742)),(1974,some (fanBlockRows 743)),(1975,some (fanBlockRows 744)),(1976,some (fanBlockRows 745)),(1977,some (fanBlockRows 746)),(1978,some (fanBlockRows 747)),(1979,some (fanBlockRows 748)),(1980,some (fanBlockRows 749)),(1981,some (fanBlockRows 750)),(1982,some (fanBlockRows 751)),(1983,some (fanBlockRows 752)),(1984,some (fanBlockRows 753)),(1985,some (fanBlockRows 754)),(1986,some (fanBlockRows 755)),(1987,some (fanBlockRows 756)),(1988,some (fanBlockRows 757)),(1989,some (fanBlockRows 758)),(1990,some (fanBlockRows 759)),(1991,some (fanBlockRows 760)),(1992,some (fanBlockRows 761)),(1993,some (fanBlockRows 762)),(1994,some (fanBlockRows 763)),(1995,some (fanBlockRows 764)),(1996,some (fanBlockRows 765)),(1997,some (fanBlockRows 766)),(1998,some (fanBlockRows 767)),(1999,some (fanBlockRows 768)),(2000,some (fanBlockRows 769)),(2001,some (fanBlockRows 770)),(2002,some (fanBlockRows 771)),(2003,some (fanBlockRows 772)),(2004,some (fanBlockRows 773)),(2005,some (fanBlockRows 774)),(2006,some (fanBlockRows 775)),(2007,some (fanBlockRows 776)),(2008,some (fanBlockRows 777)),(2009,some (fanBlockRows 778)),(2010,some (fanBlockRows 779)),(2011,some (fanBlockRows 780)),(2012,some (fanBlockRows 781)),(2013,some (fanBlockRows 782)),(2014,some (fanBlockRows 783)),(2015,some (fanBlockRows 784)),(2016,some (fanBlockRows 785)),(2017,some (fanBlockRows 786)),(2018,some (fanBlockRows 787)),(2019,some (fanBlockRows 788)),(2020,some (fanBlockRows 789)),(2021,some (fanBlockRows 790)),(2022,some (fanBlockRows 791)),(2023,some (fanBlockRows 792)),(2024,some (fanBlockRows 793)),(2025,some (fanBlockRows 794)),(2026,some (fanBlockRows 795)),(2027,some (fanBlockRows 796)),(2028,some (fanBlockRows 797)),(2029,some (fanBlockRows 799)),(2030,some (fanBlockRows 800)),(2031,some (fanBlockRows 801)),(2032,some (fanBlockRows 802)),(2033,some (fanBlockRows 803)),(2034,some (fanBlockRows 804)),(2035,some (fanBlockRows 805)),(2036,some (fanBlockRows 806)),(2037,some (fanBlockRows 807)),(2038,some (fanBlockRows 808)),(2039,some (fanBlockRows 701)),(2040,some (fanBlockRows 702)),(2041,some (fanBlockRows 703)),(2042,some (fanBlockRows 704)),(2043,some (fanBlockRows 705)),(2044,some (fanBlockRows 706)),(2045,some (fanBlockRows 707)),(2046,some (fanBlockRows 708)),(2047,some (fanBlockRows 709)),(2048,some (fanBlockRows 710)),(2049,some (fanBlockRows 712)),(2050,some (fanBlockRows 713)),(2051,some (fanBlockRows 714)),(2052,some (fanBlockRows 715)),(2053,some (fanBlockRows 716)),(2054,some (fanBlockRows 717)),(2055,some (fanBlockRows 718)),(2056,none),(2057,none),(2058,none),(2059,none),(2060,none),(2061,none),(2062,none),(2063,none),(2064,none),(2065,none),(2066,none)]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step00.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 114).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain9_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step00.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step00.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain9_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain9_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step00
