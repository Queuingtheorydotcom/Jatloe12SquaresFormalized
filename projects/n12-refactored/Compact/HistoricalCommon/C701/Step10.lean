import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C701.DirectPruning.Step10
import Compact.HistoricalCommon.C701.Step10Groups00
import Compact.HistoricalCommon.C701.Step10Groups01
import Compact.HistoricalCommon.C701.Step10Groups02
import Compact.HistoricalCommon.C701.Step10Groups03
import Compact.HistoricalCommon.C701.Step10Groups04
import Compact.HistoricalCommon.C701.Step10Groups05
import Compact.HistoricalCommon.C701.Step10Groups06
import Compact.HistoricalCommon.C701.Step10Groups07
import Compact.HistoricalCommon.C701.Step10Groups08
import Compact.HistoricalCommon.C701.Step10Groups09
import Compact.HistoricalCommon.C701.Step10Groups10

namespace N12Compact.HistoricalCommon.C701.Step10
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
  (.sourceCut 29 (.neighborCut 11 (.sourceCut 7 (.neighborCut 5 .leaf (.neighborCut 3 .leaf .leaf)) (.sourceCut 3 .leaf (.sourceCut 4 .leaf (.sourceCut 7 .leaf (.neighborCut 5 .leaf (.sourceCut 4 .leaf .leaf)))))) (.neighborCut 5 (.sourceCut 7 .leaf (.sourceCut 7 .leaf (.sourceCut 7 .leaf (.sourceCut 4 .leaf .leaf)))) (.neighborCut 6 (.sourceCut 14 .leaf .leaf) (.neighborCut 11 .leaf (.sourceCut 14 (.neighborCut 6 .leaf .leaf) (.sourceCut 7 (.neighborCut 6 .leaf .leaf) (.neighborCut 6 (.sourceCut 4 .leaf .leaf) .leaf))))))) (.neighborCut 5 (.sourceCut 7 .leaf (.sourceCut 8 .leaf (.sourceCut 7 .leaf .leaf))) (.neighborCut 6 (.sourceCut 7 (.neighborCut 3 .leaf .leaf) (.sourceCut 8 (.neighborCut 3 .leaf .leaf) (.sourceCut 3 .leaf (.sourceCut 4 .leaf .leaf)))) (.neighborCut 11 .leaf (.neighborCut 11 .leaf (.sourceCut 15 .leaf (.sourceCut 7 .leaf (.neighborCut 6 (.sourceCut 4 .leaf .leaf) .leaf))))))))

theorem partition_checked : partition.Check ⟨0,59,0,45⟩ scopes := by decide +kernel

theorem covered (i : Fin 59) (j : Fin 45) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 59) (j : Fin 45) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context255_header,context266_header,context270_header,context271_header,context272_header,context273_header,context170_header,context216_header,context217_header,context218_header,context219_header,context220_header,context221_header,context222_header,context223_header,context224_header,context225_header,context226_header,context227_header,context228_header,context229_header,context230_header,context231_header,context232_header,context233_header,context234_header,context235_header,context236_header,context237_header,context238_header,context239_header,context240_header,context241_header,context242_header,context243_header,context244_header,context245_header,context246_header,context247_header,context248_header,context249_header,context250_header,context251_header,context252_header,context253_header,context254_header,context256_header,context257_header,context258_header,context259_header,context260_header,context261_header,context262_header,context263_header,context264_header,context265_header,context267_header,context268_header,context269_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 59).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(1253,none),(1254,none),(1255,none),(1256,none),(1257,some (fanBlockRows 137)),(1258,some (fanBlockRows 148)),(1259,some (fanBlockRows 152)),(1260,some (fanBlockRows 153)),(1261,some (fanBlockRows 154)),(1262,some (fanBlockRows 155)),(1263,some (fanBlockRows 98)),(1264,some (fanBlockRows 99)),(1265,some (fanBlockRows 100)),(1266,some (fanBlockRows 101)),(1267,some (fanBlockRows 102)),(1268,some (fanBlockRows 103)),(1269,some (fanBlockRows 104)),(1270,some (fanBlockRows 105)),(1271,some (fanBlockRows 106)),(1272,some (fanBlockRows 107)),(1273,some (fanBlockRows 108)),(1274,some (fanBlockRows 109)),(1275,some (fanBlockRows 110)),(1276,some (fanBlockRows 111)),(1277,some (fanBlockRows 112)),(1278,some (fanBlockRows 113)),(1279,some (fanBlockRows 114)),(1280,some (fanBlockRows 115)),(1281,some (fanBlockRows 116)),(1282,some (fanBlockRows 59)),(1283,some (fanBlockRows 117)),(1284,some (fanBlockRows 118)),(1285,some (fanBlockRows 119)),(1286,some (fanBlockRows 120)),(1287,some (fanBlockRows 121)),(1288,some (fanBlockRows 122)),(1289,some (fanBlockRows 123)),(1290,some (fanBlockRows 124)),(1291,some (fanBlockRows 125)),(1292,some (fanBlockRows 126)),(1293,some (fanBlockRows 127)),(1294,some (fanBlockRows 128)),(1295,some (fanBlockRows 129)),(1296,some (fanBlockRows 130)),(1297,some (fanBlockRows 131)),(1298,some (fanBlockRows 132)),(1299,some (fanBlockRows 133)),(1300,some (fanBlockRows 134)),(1301,some (fanBlockRows 135)),(1302,some (fanBlockRows 136)),(1303,some (fanBlockRows 138)),(1304,some (fanBlockRows 139)),(1305,some (fanBlockRows 140)),(1306,some (fanBlockRows 141)),(1307,some (fanBlockRows 142)),(1308,some (fanBlockRows 143)),(1309,some (fanBlockRows 144)),(1310,some (fanBlockRows 145)),(1311,some (fanBlockRows 146)),(1312,some (fanBlockRows 147)),(1313,some (fanBlockRows 149)),(1314,some (fanBlockRows 150)),(1315,some (fanBlockRows 151)),(1316,none)]

theorem planHeaders_exact :
    N12Compact.C701DirectPruning.Step10.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 45).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C701.continuousScout701Domain1_3Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C701DirectPruning.Step10.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C701DirectPruning.Step10.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C701.continuousScout701Domain1_3Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C701.continuousScout701Domain1_3Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C701.Step10
