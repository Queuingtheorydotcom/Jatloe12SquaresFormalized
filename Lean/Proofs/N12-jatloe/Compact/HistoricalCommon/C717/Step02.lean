import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C717.DirectPruning.Step02
import Compact.HistoricalCommon.C717.Step02Groups00
import Compact.HistoricalCommon.C717.Step02Groups01
import Compact.HistoricalCommon.C717.Step02Groups02
import Compact.HistoricalCommon.C717.Step02Groups03
import Compact.HistoricalCommon.C717.Step02Groups04
import Compact.HistoricalCommon.C717.Step02Groups05
import Compact.HistoricalCommon.C717.Step02Groups06
import Compact.HistoricalCommon.C717.Step02Groups07
import Compact.HistoricalCommon.C717.Step02Groups08
import Compact.HistoricalCommon.C717.Step02Groups09
import Compact.HistoricalCommon.C717.Step02Groups10

namespace N12Compact.HistoricalCommon.C717.Step02
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 32 (.neighborCut 28 (.sourceCut 16 .leaf (.neighborCut 14 .leaf .leaf)) (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.sourceCut 8 (.neighborCut 28 .leaf (.sourceCut 4 .leaf .leaf)) (.sourceCut 8 .leaf .leaf)))))) (.sourceCut 32 (.neighborCut 14 (.sourceCut 16 .leaf .leaf) (.neighborCut 14 (.sourceCut 16 .leaf .leaf) (.neighborCut 14 (.sourceCut 16 .leaf (.neighborCut 7 .leaf .leaf)) (.neighborCut 14 .leaf (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.sourceCut 4 .leaf .leaf))))))) (.sourceCut 32 (.neighborCut 28 .leaf (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf .leaf)))) (.neighborCut 28 (.sourceCut 16 (.neighborCut 14 .leaf .leaf) .leaf) (.neighborCut 7 .leaf (.neighborCut 7 .leaf (.neighborCut 14 .leaf (.sourceCut 16 (.neighborCut 14 .leaf (.neighborCut 14 (.sourceCut 8 .leaf .leaf) (.neighborCut 14 .leaf .leaf))) (.neighborCut 28 .leaf (.neighborCut 14 (.sourceCut 8 .leaf .leaf) .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,128,0,113⟩ scopes := by decide +kernel

theorem covered (i : Fin 128) (j : Fin 113) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 128) (j : Fin 113) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context5129_header,context5171_header,context5182_header,context5193_header,context5204_header,context5215_header,context5226_header,context5237_header,context5248_header,context5259_header,context5143_header,context5154_header,context5163_header,context5164_header,context5165_header,context5166_header,context5167_header,context5168_header,context5169_header,context5170_header,context5172_header,context5173_header,context5174_header,context5175_header,context5176_header,context5177_header,context5178_header,context5179_header,context5180_header,context5181_header,context5183_header,context5184_header,context5185_header,context5186_header,context5187_header,context5188_header,context5189_header,context5190_header,context5191_header,context5192_header,context5194_header,context5195_header,context5196_header,context5197_header,context5198_header,context5199_header,context5200_header,context5201_header,context5202_header,context5203_header,context5205_header,context5206_header,context5207_header,context5208_header,context5209_header,context5210_header,context5211_header,context5212_header,context5213_header,context5214_header,context5216_header,context5217_header,context5218_header,context5219_header,context5220_header,context5221_header,context5222_header,context5223_header,context5224_header,context5225_header,context5227_header,context5228_header,context5229_header,context5230_header,context5231_header,context5232_header,context5233_header,context5234_header,context5235_header,context5236_header,context5238_header,context5239_header,context5240_header,context5241_header,context5242_header,context5243_header,context5244_header,context5245_header,context5246_header,context5247_header,context5249_header,context5250_header,context5251_header,context5252_header,context5253_header,context5254_header,context5255_header,context5256_header,context5257_header,context5258_header,context5133_header,context5134_header,context5135_header,context5136_header,context5137_header,context5138_header,context5139_header,context5140_header,context5141_header,context5142_header,context5144_header,context5145_header,context5146_header,context5147_header,context5148_header,context5149_header,context5150_header,context5151_header,context5152_header,context5153_header,context5155_header,context5156_header,context5157_header,context5158_header,context5159_header,context5160_header,context5161_header,context5162_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 128).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(4277,some (fanBlockRows 1914)),(4278,some (fanBlockRows 1953)),(4279,some (fanBlockRows 1964)),(4280,some (fanBlockRows 1973)),(4281,some (fanBlockRows 1974)),(4282,some (fanBlockRows 1975)),(4283,some (fanBlockRows 1976)),(4284,some (fanBlockRows 1985)),(4285,some (fanBlockRows 1996)),(4286,some (fanBlockRows 2007)),(4287,some (fanBlockRows 1925)),(4288,some (fanBlockRows 1936)),(4289,some (fanBlockRows 1945)),(4290,some (fanBlockRows 1946)),(4291,some (fanBlockRows 1947)),(4292,some (fanBlockRows 1948)),(4293,some (fanBlockRows 1949)),(4294,some (fanBlockRows 1950)),(4295,some (fanBlockRows 1951)),(4296,some (fanBlockRows 1952)),(4297,some (fanBlockRows 1954)),(4298,some (fanBlockRows 1955)),(4299,some (fanBlockRows 1956)),(4300,some (fanBlockRows 1957)),(4301,some (fanBlockRows 1958)),(4302,some (fanBlockRows 1959)),(4303,some (fanBlockRows 1960)),(4304,some (fanBlockRows 1961)),(4305,some (fanBlockRows 1962)),(4306,some (fanBlockRows 1963)),(4307,some (fanBlockRows 1965)),(4308,some (fanBlockRows 1966)),(4309,some (fanBlockRows 1967)),(4310,some (fanBlockRows 1968)),(4311,some (fanBlockRows 1969)),(4312,some (fanBlockRows 1970)),(4313,some (fanBlockRows 1971)),(4314,some (fanBlockRows 1972)),(4315,some (fanBlockRows 59)),(4316,some (fanBlockRows 59)),(4317,some (fanBlockRows 59)),(4318,some (fanBlockRows 59)),(4319,some (fanBlockRows 59)),(4320,some (fanBlockRows 59)),(4321,some (fanBlockRows 59)),(4322,some (fanBlockRows 59)),(4323,some (fanBlockRows 59)),(4324,some (fanBlockRows 59)),(4325,some (fanBlockRows 59)),(4326,some (fanBlockRows 59)),(4327,some (fanBlockRows 59)),(4328,some (fanBlockRows 59)),(4329,some (fanBlockRows 59)),(4330,some (fanBlockRows 59)),(4331,some (fanBlockRows 59)),(4332,some (fanBlockRows 59)),(4333,some (fanBlockRows 59)),(4334,some (fanBlockRows 59)),(4335,some (fanBlockRows 59)),(4336,some (fanBlockRows 59)),(4337,some (fanBlockRows 59)),(4338,some (fanBlockRows 59)),(4339,some (fanBlockRows 59)),(4340,some (fanBlockRows 59)),(4341,some (fanBlockRows 59)),(4342,some (fanBlockRows 59)),(4343,some (fanBlockRows 59)),(4344,some (fanBlockRows 59)),(4345,some (fanBlockRows 59)),(4346,some (fanBlockRows 59)),(4347,some (fanBlockRows 59)),(4348,some (fanBlockRows 59)),(4349,some (fanBlockRows 1977)),(4350,some (fanBlockRows 1978)),(4351,some (fanBlockRows 1979)),(4352,some (fanBlockRows 1980)),(4353,some (fanBlockRows 1981)),(4354,some (fanBlockRows 1982)),(4355,some (fanBlockRows 1983)),(4356,some (fanBlockRows 1984)),(4357,some (fanBlockRows 1986)),(4358,some (fanBlockRows 1987)),(4359,some (fanBlockRows 1988)),(4360,some (fanBlockRows 1989)),(4361,some (fanBlockRows 1990)),(4362,some (fanBlockRows 1991)),(4363,some (fanBlockRows 1992)),(4364,some (fanBlockRows 1993)),(4365,some (fanBlockRows 1994)),(4366,some (fanBlockRows 1995)),(4367,some (fanBlockRows 1997)),(4368,some (fanBlockRows 1998)),(4369,some (fanBlockRows 1999)),(4370,some (fanBlockRows 2000)),(4371,some (fanBlockRows 2001)),(4372,some (fanBlockRows 2002)),(4373,some (fanBlockRows 2003)),(4374,some (fanBlockRows 2004)),(4375,some (fanBlockRows 2005)),(4376,some (fanBlockRows 2006)),(4377,some (fanBlockRows 1915)),(4378,some (fanBlockRows 1916)),(4379,some (fanBlockRows 1917)),(4380,some (fanBlockRows 1918)),(4381,some (fanBlockRows 1919)),(4382,some (fanBlockRows 1920)),(4383,some (fanBlockRows 1921)),(4384,some (fanBlockRows 1922)),(4385,some (fanBlockRows 1923)),(4386,some (fanBlockRows 1924)),(4387,some (fanBlockRows 1926)),(4388,some (fanBlockRows 1927)),(4389,some (fanBlockRows 1928)),(4390,some (fanBlockRows 1929)),(4391,some (fanBlockRows 1930)),(4392,some (fanBlockRows 1931)),(4393,some (fanBlockRows 1932)),(4394,some (fanBlockRows 1933)),(4395,some (fanBlockRows 1934)),(4396,some (fanBlockRows 1935)),(4397,some (fanBlockRows 1937)),(4398,some (fanBlockRows 1938)),(4399,some (fanBlockRows 1939)),(4400,some (fanBlockRows 1940)),(4401,some (fanBlockRows 1941)),(4402,some (fanBlockRows 1942)),(4403,some (fanBlockRows 1943)),(4404,some (fanBlockRows 1944))]

theorem planHeaders_exact :
    N12Compact.C717DirectPruning.Step02.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 113).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C717.continuousScout717Domain10_0Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C717DirectPruning.Step02.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C717DirectPruning.Step02.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C717.continuousScout717Domain10_0Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C717.continuousScout717Domain10_0Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C717.Step02
