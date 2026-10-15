import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step11
import Compact.HistoricalCommon.C701.Step11Groups00
import Compact.HistoricalCommon.C701.Step11Groups01
import Compact.HistoricalCommon.C701.Step11Groups02
import Compact.HistoricalCommon.C701.Step11Groups03
import Compact.HistoricalCommon.C701.Step11Groups04
import Compact.HistoricalCommon.C701.Step11Groups05
import Compact.HistoricalCommon.C701.Step11Groups06
import Compact.HistoricalCommon.C701.Step11Groups07

namespace N12Compact.HistoricalCommon.C701.Step11
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 15 (.neighborCut 5 (.sourceCut 7 .leaf .leaf) (.neighborCut 3 (.sourceCut 7 .leaf .leaf) (.neighborCut 3 (.sourceCut 7 .leaf .leaf) (.neighborCut 11 (.sourceCut 7 (.neighborCut 5 .leaf (.sourceCut 3 .leaf .leaf)) .leaf) (.neighborCut 11 .leaf (.sourceCut 7 (.neighborCut 6 .leaf (.neighborCut 3 .leaf .leaf)) .leaf)))))) (.sourceCut 16 (.neighborCut 11 (.sourceCut 4 .leaf (.sourceCut 4 .leaf .leaf)) (.neighborCut 11 .leaf .leaf)) (.sourceCut 16 .leaf (.sourceCut 8 .leaf (.neighborCut 5 .leaf (.neighborCut 3 .leaf (.neighborCut 3 .leaf (.neighborCut 11 (.sourceCut 4 .leaf .leaf) (.neighborCut 11 .leaf (.neighborCut 6 .leaf (.sourceCut 4 .leaf .leaf)))))))))))

theorem partition_checked : partition.Check ⟨0,63,0,45⟩ scopes := by decide +kernel

theorem covered (i : Fin 63) (j : Fin 45) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 63) (j : Fin 45) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context274_header,context362_header,context373_header,context384_header,context395_header,context406_header,context410_header,context411_header,context412_header,context413_header,context352_header,context353_header,context354_header,context355_header,context356_header,context357_header,context358_header,context359_header,context360_header,context361_header,context363_header,context364_header,context365_header,context366_header,context367_header,context368_header,context369_header,context370_header,context371_header,context372_header,context374_header,context375_header,context376_header,context377_header,context378_header,context379_header,context380_header,context381_header,context382_header,context383_header,context385_header,context386_header,context387_header,context388_header,context389_header,context390_header,context391_header,context392_header,context393_header,context394_header,context396_header,context397_header,context398_header,context399_header,context400_header,context401_header,context402_header,context403_header,context404_header,context405_header,context407_header,context408_header,context409_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 63).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1317,some (fanBlockRows 156)),(1318,some (fanBlockRows 157)),(1319,some (fanBlockRows 158)),(1320,some (fanBlockRows 159)),(1321,some (fanBlockRows 160)),(1322,some (fanBlockRows 161)),(1323,some (fanBlockRows 165)),(1324,some (fanBlockRows 59)),(1325,some (fanBlockRows 59)),(1326,some (fanBlockRows 59)),(1327,some (fanBlockRows 59)),(1328,some (fanBlockRows 59)),(1329,some (fanBlockRows 59)),(1330,some (fanBlockRows 59)),(1331,some (fanBlockRows 59)),(1332,some (fanBlockRows 59)),(1333,some (fanBlockRows 59)),(1334,some (fanBlockRows 59)),(1335,some (fanBlockRows 59)),(1336,some (fanBlockRows 59)),(1337,some (fanBlockRows 59)),(1338,some (fanBlockRows 59)),(1339,some (fanBlockRows 59)),(1340,some (fanBlockRows 59)),(1341,some (fanBlockRows 59)),(1342,some (fanBlockRows 59)),(1343,some (fanBlockRows 59)),(1344,some (fanBlockRows 59)),(1345,some (fanBlockRows 59)),(1346,some (fanBlockRows 59)),(1347,some (fanBlockRows 59)),(1348,some (fanBlockRows 59)),(1349,some (fanBlockRows 59)),(1350,some (fanBlockRows 59)),(1351,some (fanBlockRows 59)),(1352,some (fanBlockRows 59)),(1353,some (fanBlockRows 59)),(1354,some (fanBlockRows 59)),(1355,some (fanBlockRows 59)),(1356,some (fanBlockRows 59)),(1357,some (fanBlockRows 59)),(1358,some (fanBlockRows 59)),(1359,some (fanBlockRows 59)),(1360,some (fanBlockRows 59)),(1361,some (fanBlockRows 59)),(1362,some (fanBlockRows 59)),(1363,some (fanBlockRows 59)),(1364,some (fanBlockRows 59)),(1365,some (fanBlockRows 59)),(1366,some (fanBlockRows 59)),(1367,some (fanBlockRows 59)),(1368,some (fanBlockRows 59)),(1369,some (fanBlockRows 59)),(1370,some (fanBlockRows 59)),(1371,some (fanBlockRows 59)),(1372,some (fanBlockRows 59)),(1373,some (fanBlockRows 59)),(1374,some (fanBlockRows 59)),(1375,some (fanBlockRows 59)),(1376,some (fanBlockRows 59)),(1377,some (fanBlockRows 162)),(1378,some (fanBlockRows 163)),(1379,some (fanBlockRows 164))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step11.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 45).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain7_9Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step11.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step11.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain7_9Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain7_9Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step11
