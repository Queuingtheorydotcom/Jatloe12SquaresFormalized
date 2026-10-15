import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step29
import Compact.HistoricalCommon.C701.Step29Groups00
import Compact.HistoricalCommon.C701.Step29Groups01
import Compact.HistoricalCommon.C701.Step29Groups02
import Compact.HistoricalCommon.C701.Step29Groups03
import Compact.HistoricalCommon.C701.Step29Groups04
import Compact.HistoricalCommon.C701.Step29Groups05
import Compact.HistoricalCommon.C701.Step29Groups06
import Compact.HistoricalCommon.C701.Step29Groups07
import Compact.HistoricalCommon.C701.Step29Groups08
import Compact.HistoricalCommon.C701.Step29Groups09

namespace N12Compact.HistoricalCommon.C701.Step29
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33,group34,group35,group36]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope,group34_scope,group35_scope,group36_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 4 (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf)) (.sourceCut 4 (.neighborCut 3 (.sourceCut 2 .leaf (.neighborCut 1 .leaf .leaf)) (.neighborCut 2 .leaf .leaf)) (.sourceCut 4 (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf .leaf))) (.sourceCut 4 (.neighborCut 1 .leaf (.neighborCut 2 .leaf .leaf)) (.sourceCut 16 .leaf (.sourceCut 16 (.neighborCut 3 .leaf (.neighborCut 2 .leaf .leaf)) (.sourceCut 4 (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf .leaf))) (.sourceCut 4 (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf .leaf))) (.sourceCut 4 (.neighborCut 1 .leaf (.neighborCut 2 .leaf (.neighborCut 2 .leaf .leaf))) (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf (.neighborCut 1 .leaf .leaf))))))))))))))

theorem partition_checked : partition.Check ⟨0,64,0,7⟩ scopes := by decide +kernel

theorem covered (i : Fin 64) (j : Fin 7) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 64) (j : Fin 7) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context1258_header,context1269_header,context1280_header,context1291_header,context1302_header,context1313_header,context1318_header,context1319_header,context1320_header,context1321_header,context1259_header,context1260_header,context1261_header,context1262_header,context1263_header,context1264_header,context1265_header,context1266_header,context1267_header,context1268_header,context1270_header,context1271_header,context1272_header,context1273_header,context1274_header,context1275_header,context1276_header,context1277_header,context1278_header,context1279_header,context1281_header,context1282_header,context1283_header,context1284_header,context1285_header,context1286_header,context1287_header,context1288_header,context1289_header,context1290_header,context1292_header,context1293_header,context1294_header,context1295_header,context1296_header,context1297_header,context1298_header,context1299_header,context1300_header,context1301_header,context1303_header,context1304_header,context1305_header,context1306_header,context1307_header,context1308_header,context1309_header,context1310_header,context1311_header,context1312_header,context1314_header,context1315_header,context1316_header,context1317_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 64).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(943,some (fanBlockRows 483)),(944,some (fanBlockRows 489)),(945,some (fanBlockRows 490)),(946,some (fanBlockRows 491)),(947,some (fanBlockRows 494)),(948,some (fanBlockRows 505)),(949,some (fanBlockRows 510)),(950,some (fanBlockRows 511)),(951,some (fanBlockRows 512)),(952,some (fanBlockRows 513)),(953,some (fanBlockRows 484)),(954,some (fanBlockRows 485)),(955,some (fanBlockRows 486)),(956,some (fanBlockRows 487)),(957,some (fanBlockRows 488)),(958,some (fanBlockRows 59)),(959,some (fanBlockRows 59)),(960,some (fanBlockRows 59)),(961,some (fanBlockRows 59)),(962,some (fanBlockRows 59)),(963,some (fanBlockRows 59)),(964,some (fanBlockRows 59)),(965,some (fanBlockRows 59)),(966,some (fanBlockRows 59)),(967,some (fanBlockRows 59)),(968,some (fanBlockRows 59)),(969,some (fanBlockRows 59)),(970,some (fanBlockRows 59)),(971,some (fanBlockRows 59)),(972,some (fanBlockRows 59)),(973,some (fanBlockRows 59)),(974,some (fanBlockRows 59)),(975,some (fanBlockRows 59)),(976,some (fanBlockRows 59)),(977,some (fanBlockRows 59)),(978,some (fanBlockRows 59)),(979,some (fanBlockRows 59)),(980,some (fanBlockRows 59)),(981,some (fanBlockRows 59)),(982,some (fanBlockRows 59)),(983,some (fanBlockRows 59)),(984,some (fanBlockRows 59)),(985,some (fanBlockRows 59)),(986,some (fanBlockRows 59)),(987,some (fanBlockRows 59)),(988,some (fanBlockRows 59)),(989,some (fanBlockRows 59)),(990,some (fanBlockRows 59)),(991,some (fanBlockRows 492)),(992,some (fanBlockRows 493)),(993,some (fanBlockRows 495)),(994,some (fanBlockRows 496)),(995,some (fanBlockRows 497)),(996,some (fanBlockRows 498)),(997,some (fanBlockRows 499)),(998,some (fanBlockRows 500)),(999,some (fanBlockRows 501)),(1000,some (fanBlockRows 502)),(1001,some (fanBlockRows 503)),(1002,some (fanBlockRows 504)),(1003,some (fanBlockRows 506)),(1004,some (fanBlockRows 507)),(1005,some (fanBlockRows 508)),(1006,some (fanBlockRows 509))]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step29.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 7).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain7_24Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step29.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step29.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain7_24Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain7_24Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step29
