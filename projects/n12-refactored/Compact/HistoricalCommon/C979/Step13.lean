import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C979.DirectPruning.Step13
import Compact.HistoricalCommon.C979.Step13Groups00
import Compact.HistoricalCommon.C979.Step13Groups01
import Compact.HistoricalCommon.C979.Step13Groups02
import Compact.HistoricalCommon.C979.Step13Groups03
import Compact.HistoricalCommon.C979.Step13Groups04
import Compact.HistoricalCommon.C979.Step13Groups05
import Compact.HistoricalCommon.C979.Step13Groups06
import Compact.HistoricalCommon.C979.Step13Groups07

namespace N12Compact.HistoricalCommon.C979.Step13
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
  (.neighborCut 13 (.sourceCut 20 .leaf (.sourceCut 21 (.neighborCut 6 .leaf .leaf) (.neighborCut 6 (.sourceCut 21 .leaf .leaf) .leaf))) (.neighborCut 14 .leaf (.neighborCut 27 .leaf (.sourceCut 20 (.neighborCut 27 (.sourceCut 10 .leaf (.sourceCut 5 .leaf .leaf)) (.neighborCut 14 (.sourceCut 10 .leaf (.sourceCut 5 .leaf .leaf)) .leaf)) (.sourceCut 21 (.neighborCut 27 .leaf (.neighborCut 14 .leaf (.sourceCut 10 (.neighborCut 7 .leaf .leaf) .leaf))) (.sourceCut 21 (.neighborCut 13 .leaf (.neighborCut 14 (.sourceCut 10 .leaf .leaf) .leaf)) (.neighborCut 27 .leaf (.sourceCut 10 (.neighborCut 14 .leaf .leaf) (.neighborCut 14 (.sourceCut 5 .leaf .leaf) (.neighborCut 7 .leaf .leaf))))))))))

theorem partition_checked : partition.Check ⟨0,83,0,109⟩ scopes := by decide +kernel

theorem covered (i : Fin 83) (j : Fin 109) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 83) (j : Fin 109) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context10376_header,context10386_header,context10396_header,context10407_header,context10418_header,context10429_header,context10437_header,context10438_header,context10248_header,context10358_header,context10359_header,context10360_header,context10361_header,context10362_header,context10363_header,context10364_header,context10365_header,context10366_header,context10367_header,context10368_header,context10369_header,context10370_header,context10371_header,context10372_header,context10373_header,context10374_header,context10375_header,context10377_header,context10378_header,context10379_header,context10380_header,context10381_header,context10382_header,context10383_header,context10384_header,context10385_header,context10387_header,context10388_header,context10389_header,context10390_header,context10391_header,context10392_header,context10393_header,context10394_header,context9957_header,context10395_header,context10397_header,context10398_header,context10399_header,context10400_header,context10401_header,context10402_header,context10403_header,context10404_header,context10405_header,context10406_header,context10408_header,context10409_header,context10410_header,context10411_header,context10412_header,context10413_header,context10414_header,context10415_header,context10416_header,context10417_header,context10419_header,context10420_header,context10421_header,context10422_header,context10423_header,context10424_header,context10425_header,context10426_header,context10427_header,context10428_header,context10430_header,context10431_header,context10432_header,context10433_header,context10434_header,context10435_header,context10436_header]

theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 83).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(11862,none),(11863,none),(11864,some (fanBlockRows 4394)),(11865,some (fanBlockRows 4404)),(11866,some (fanBlockRows 4414)),(11867,some (fanBlockRows 4425)),(11868,some (fanBlockRows 4436)),(11869,some (fanBlockRows 4447)),(11870,some (fanBlockRows 4455)),(11871,some (fanBlockRows 4456)),(11872,some (fanBlockRows 4375)),(11873,some (fanBlockRows 4376)),(11874,some (fanBlockRows 4377)),(11875,some (fanBlockRows 4378)),(11876,some (fanBlockRows 4379)),(11877,some (fanBlockRows 4380)),(11878,some (fanBlockRows 4381)),(11879,some (fanBlockRows 4382)),(11880,some (fanBlockRows 4383)),(11881,some (fanBlockRows 4384)),(11882,some (fanBlockRows 4385)),(11883,some (fanBlockRows 4386)),(11884,some (fanBlockRows 4387)),(11885,some (fanBlockRows 4388)),(11886,some (fanBlockRows 4389)),(11887,some (fanBlockRows 4390)),(11888,some (fanBlockRows 4391)),(11889,some (fanBlockRows 4392)),(11890,none),(11891,some (fanBlockRows 4393)),(11892,some (fanBlockRows 4395)),(11893,some (fanBlockRows 4396)),(11894,some (fanBlockRows 4397)),(11895,some (fanBlockRows 4398)),(11896,some (fanBlockRows 4399)),(11897,none),(11898,some (fanBlockRows 4400)),(11899,some (fanBlockRows 4401)),(11900,some (fanBlockRows 4402)),(11901,some (fanBlockRows 4403)),(11902,some (fanBlockRows 4405)),(11903,some (fanBlockRows 4406)),(11904,some (fanBlockRows 4407)),(11905,some (fanBlockRows 4408)),(11906,some (fanBlockRows 4409)),(11907,some (fanBlockRows 4410)),(11908,some (fanBlockRows 4411)),(11909,some (fanBlockRows 4412)),(11910,some (fanBlockRows 59)),(11911,some (fanBlockRows 4413)),(11912,some (fanBlockRows 4415)),(11913,some (fanBlockRows 4416)),(11914,some (fanBlockRows 4417)),(11915,some (fanBlockRows 4418)),(11916,some (fanBlockRows 4419)),(11917,some (fanBlockRows 4420)),(11918,some (fanBlockRows 4421)),(11919,some (fanBlockRows 4422)),(11920,some (fanBlockRows 4423)),(11921,some (fanBlockRows 4424)),(11922,some (fanBlockRows 4426)),(11923,some (fanBlockRows 4427)),(11924,some (fanBlockRows 4428)),(11925,some (fanBlockRows 4429)),(11926,some (fanBlockRows 4430)),(11927,some (fanBlockRows 4431)),(11928,some (fanBlockRows 4432)),(11929,some (fanBlockRows 4433)),(11930,some (fanBlockRows 4434)),(11931,some (fanBlockRows 4435)),(11932,some (fanBlockRows 4437)),(11933,some (fanBlockRows 4438)),(11934,some (fanBlockRows 4439)),(11935,some (fanBlockRows 4440)),(11936,some (fanBlockRows 4441)),(11937,some (fanBlockRows 4442)),(11938,some (fanBlockRows 4443)),(11939,some (fanBlockRows 4444)),(11940,some (fanBlockRows 4445)),(11941,some (fanBlockRows 4446)),(11942,some (fanBlockRows 4448)),(11943,some (fanBlockRows 4449)),(11944,some (fanBlockRows 4450)),(11945,some (fanBlockRows 4451)),(11946,some (fanBlockRows 4452)),(11947,some (fanBlockRows 4453)),(11948,some (fanBlockRows 4454)),(11949,none),(11950,none),(11951,none),(11952,none),(11953,none),(11954,none),(11955,none)]

theorem planHeaders_exact :
    N12Compact.C979DirectPruning.Step13.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 109).map (fun j => (neighbors j).header.pose) = N12Compact.Preservation.C979.continuousScout979Domain5_10Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C979DirectPruning.Step13.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C979DirectPruning.Step13.planHeaders, HeaderOverlap dictionary N12Compact.Preservation.C979.continuousScout979Domain5_10Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.Preservation.C979.continuousScout979Domain5_10Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C979.Step13
