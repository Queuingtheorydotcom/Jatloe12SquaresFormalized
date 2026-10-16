import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step17
import Compact.HistoricalCommon.C701.Step17Groups00
import Compact.HistoricalCommon.C701.Step17Groups01
import Compact.HistoricalCommon.C701.Step17Groups02
import Compact.HistoricalCommon.C701.Step17Groups03
import Compact.HistoricalCommon.C701.Step17Groups04
import Compact.HistoricalCommon.C701.Step17Groups05
import Compact.HistoricalCommon.C701.Step17Groups06
import Compact.HistoricalCommon.C701.Step17Groups07
import Compact.HistoricalCommon.C701.Step17Groups08
import Compact.HistoricalCommon.C701.Step17Groups09
import Compact.HistoricalCommon.C701.Step17Groups10
import Compact.HistoricalCommon.C701.Step17Groups11
import Compact.HistoricalCommon.C701.Step17Groups12
import Compact.HistoricalCommon.C701.Step17Groups13
import Compact.HistoricalCommon.C701.Step17Groups14
import Compact.HistoricalCommon.C701.Step17Groups15

namespace N12Compact.HistoricalCommon.C701.Step17
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36,group37,group38,group39,group40,group41,group42,group43,group44,group45,group46,group47,group48,group49,group50,group51,group52,group53,group54,group55,group56,group57,group58,group59,group60]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope,group37_scope,group38_scope,group39_scope,group40_scope,group41_scope,group42_scope,group43_scope,group44_scope,group45_scope,group46_scope,group47_scope,group48_scope,group49_scope,group50_scope,group51_scope,group52_scope,group53_scope,group54_scope,group55_scope,group56_scope,group57_scope,group58_scope,group59_scope,group60_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 4 (.neighborCut 6 .leaf (.sourceCut 2 .leaf .leaf)) (.sourceCut 4 .leaf (.sourceCut 4 (.neighborCut 3 .leaf (.neighborCut 3 .leaf .leaf)) (.sourceCut 4 (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.sourceCut 2 .leaf (.neighborCut 3 .leaf .leaf))))) (.sourceCut 4 (.neighborCut 3 .leaf (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf))))) (.sourceCut 4 (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf)))) (.sourceCut 8 (.neighborCut 3 (.sourceCut 4 .leaf .leaf) (.neighborCut 1 (.sourceCut 4 .leaf .leaf) (.neighborCut 2 (.sourceCut 4 .leaf .leaf) (.neighborCut 3 .leaf (.neighborCut 2 (.sourceCut 4 .leaf .leaf) .leaf))))) (.sourceCut 8 (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf)))) (.sourceCut 8 (.neighborCut 3 (.sourceCut 4 .leaf (.neighborCut 1 .leaf .leaf)) (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.sourceCut 4 .leaf .leaf))))) (.sourceCut 8 (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf)))))) (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 2 .leaf (.neighborCut 1 .leaf .leaf))))))))))))))))

theorem partition_checked : partition.Check ⟨0,64,0,13⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 13) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 13) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context665_header,context693_header,context705_header,context717_header,context729_header,context741_header,context747_header,context749_header,context751_header,context753_header,context680_header,context682_header,context684_header,context685_header,context686_header,context687_header,context688_header,context689_header,context690_header,context691_header,context694_header,context695_header,context696_header,context697_header,context698_header,context699_header,context700_header,context701_header,context702_header,context703_header,context706_header,context707_header,context708_header,context709_header,context710_header,context711_header,context712_header,context713_header,context714_header,context715_header,context718_header,context719_header,context720_header,context721_header,context722_header,context723_header,context724_header,context725_header,context726_header,context727_header,context730_header,context731_header,context732_header,context733_header,context734_header,context735_header,context736_header,context737_header,context738_header,context739_header,context742_header,context743_header,context744_header,context745_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(314,some (fanBlockRows 269)),(315,some (fanBlockRows 59)),(316,some (fanBlockRows 59)),(317,some (fanBlockRows 59)),(318,some (fanBlockRows 59)),(319,some (fanBlockRows 59)),(320,some (fanBlockRows 59)),(321,some (fanBlockRows 59)),(322,some (fanBlockRows 59)),(323,some (fanBlockRows 59)),(324,some (fanBlockRows 59)),(325,some (fanBlockRows 59)),(326,some (fanBlockRows 59)),(327,some (fanBlockRows 270)),(328,some (fanBlockRows 271)),(329,some (fanBlockRows 272)),(330,some (fanBlockRows 273)),(331,some (fanBlockRows 274)),(332,some (fanBlockRows 275)),(333,some (fanBlockRows 276)),(334,some (fanBlockRows 277)),(335,some (fanBlockRows 278)),(336,some (fanBlockRows 279)),(337,some (fanBlockRows 280)),(338,some (fanBlockRows 281)),(339,some (fanBlockRows 282)),(340,some (fanBlockRows 283)),(341,some (fanBlockRows 284)),(342,some (fanBlockRows 285)),(343,some (fanBlockRows 286)),(344,some (fanBlockRows 287)),(345,some (fanBlockRows 288)),(346,some (fanBlockRows 289)),(347,some (fanBlockRows 290)),(348,some (fanBlockRows 291)),(349,some (fanBlockRows 292)),(350,some (fanBlockRows 293)),(351,some (fanBlockRows 294)),(352,some (fanBlockRows 295)),(353,some (fanBlockRows 296)),(354,some (fanBlockRows 297)),(355,some (fanBlockRows 298)),(356,some (fanBlockRows 299)),(357,some (fanBlockRows 300)),(358,some (fanBlockRows 301)),(359,some (fanBlockRows 302)),(360,some (fanBlockRows 303)),(361,some (fanBlockRows 304)),(362,some (fanBlockRows 305)),(363,some (fanBlockRows 306)),(364,some (fanBlockRows 307)),(365,some (fanBlockRows 308)),(366,some (fanBlockRows 309)),(367,some (fanBlockRows 310)),(368,some (fanBlockRows 311)),(369,some (fanBlockRows 312)),(370,some (fanBlockRows 313)),(371,some (fanBlockRows 314)),(372,some (fanBlockRows 315)),(373,some (fanBlockRows 316)),(374,some (fanBlockRows 317)),(375,some (fanBlockRows 318)),(376,some (fanBlockRows 319)),(377,some (fanBlockRows 320))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step17.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 13).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain7_14Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step17.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step17.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain7_14Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain7_14Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step17
