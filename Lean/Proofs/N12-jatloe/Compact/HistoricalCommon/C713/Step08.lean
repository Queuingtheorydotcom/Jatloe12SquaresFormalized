import Compact.Bridge.CommonHeaderPruning
import Compact.Bridge.CommonRectanglePartition
import Compact.Cases.C713.DirectPruning.Step08
import Compact.HistoricalCommon.C713.Step08Groups00
import Compact.HistoricalCommon.C713.Step08Groups01
import Compact.HistoricalCommon.C713.Step08Groups02
import Compact.HistoricalCommon.C713.Step08Groups03
import Compact.HistoricalCommon.C713.Step08Groups04
import Compact.HistoricalCommon.C713.Step08Groups05
import Compact.HistoricalCommon.C713.Step08Groups06
import Compact.HistoricalCommon.C713.Step08Groups07
import Compact.HistoricalCommon.C713.Step08Groups08

namespace N12Compact.HistoricalCommon.C713.Step08
open S12 S12Pilot IntegerSupport IndexedCommonGroups HistoricalData C713Shared
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section

def groups : List (CheckedGroup sources neighbors) :=
  [group0,group1,group2,group3,group4,group5,group6,group7,group8,group9,group10,group11,group12,group13,group14,group15,group16,group17,group18,group19,group20,group21,group22,group23,group24,group25,group26,group27,group28,group29,group30,group31,group32,group33]

def scopes : List Scope :=
  [group0_scope,group1_scope,group2_scope,group3_scope,group4_scope,group5_scope,group6_scope,group7_scope,group8_scope,group9_scope,group10_scope,group11_scope,group12_scope,group13_scope,group14_scope,group15_scope,group16_scope,group17_scope,group18_scope,group19_scope,group20_scope,group21_scope,group22_scope,group23_scope,group24_scope,group25_scope,group26_scope,group27_scope,group28_scope,group29_scope,group30_scope,group31_scope,group32_scope,group33_scope]

theorem scopes_exact : groups.map CheckedGroup.scope = scopes := rfl

def partition : RectanglePartition :=
  (.sourceCut 50 (.neighborCut 23 (.sourceCut 12 (.neighborCut 11 .leaf .leaf) (.sourceCut 13 (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf)) (.sourceCut 12 .leaf (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf))))) (.neighborCut 24 .leaf (.neighborCut 23 .leaf (.sourceCut 25 (.neighborCut 12 .leaf .leaf) (.sourceCut 12 (.neighborCut 12 .leaf .leaf) (.neighborCut 12 .leaf .leaf)))))) (.neighborCut 23 (.sourceCut 25 .leaf (.sourceCut 13 .leaf (.neighborCut 11 .leaf .leaf))) (.neighborCut 24 .leaf (.sourceCut 25 (.neighborCut 23 (.sourceCut 12 .leaf (.neighborCut 11 .leaf (.neighborCut 6 .leaf .leaf))) .leaf) (.sourceCut 13 (.neighborCut 23 (.sourceCut 6 .leaf .leaf) .leaf) (.neighborCut 23 .leaf (.neighborCut 12 (.sourceCut 6 .leaf .leaf) .leaf)))))))

theorem partition_checked : partition.Check ⟨0,101,0,94⟩ scopes := by decide +kernel

theorem covered (i : Fin 101) (j : Fin 94) : ScopeCheck scopes i.val j.val :=
  partition.covers scopes partition_checked i j

theorem pairs (i : Fin 101) (j : Fin 94) :
    PairOverlaps (sources i) (neighbors j) :=
  groups_sound sources neighbors groups scopes scopes_exact covered i j

def sourceHeaders : List (Header dictionary) :=
  [context3505_header,context3516_header,context3527_header,context3538_header,context3457_header,context3460_header,context3461_header,context3462_header,context3463_header,context3464_header,context3465_header,context3466_header,context3467_header,context3468_header,context3469_header,context3470_header,context3471_header,context3472_header,context3473_header,context3474_header,context3475_header,context3476_header,context3477_header,context3478_header,context3479_header,context3480_header,context3481_header,context3482_header,context3483_header,context3484_header,context3485_header,context3486_header,context3487_header,context2373_header,context2375_header,context2377_header,context2379_header,context2381_header,context2383_header,context2385_header,context2387_header,context2389_header,context3488_header,context3489_header,context3490_header,context3491_header,context3492_header,context3493_header,context3494_header,context3495_header,context3496_header,context3497_header,context3498_header,context3499_header,context3500_header,context3501_header,context3502_header,context3503_header,context3504_header,context3506_header,context3507_header,context3508_header,context3509_header,context3510_header,context3511_header,context3512_header,context3513_header,context3514_header,context3515_header,context3517_header,context3518_header,context3519_header,context3520_header,context3521_header,context3522_header,context3523_header,context3524_header,context3525_header,context3526_header,context3528_header,context3529_header,context3530_header,context3531_header,context3532_header,context3533_header,context3534_header,context3535_header,context3536_header,context3537_header,context3353_header,context3448_header,context3449_header,context3450_header,context3451_header,context3452_header,context3453_header,context3454_header,context3455_header,context3456_header,context3458_header,context3459_header]

set_option maxRecDepth 10000 in
theorem sourceHeaders_exact :
    sourceHeaders = (List.finRange 101).map (fun i => (sources i).header) := rfl

def planHeaders : List (Fin poseCount × Option (List (Fin rowCount))) :=
  [(3529,none),(3530,none),(3531,none),(3532,none),(3533,none),(3534,none),(3535,some (fanBlockRows 1326)),(3536,some (fanBlockRows 1337)),(3537,some (fanBlockRows 1348)),(3538,some (fanBlockRows 1359)),(3539,some (fanBlockRows 1278)),(3540,some (fanBlockRows 1281)),(3541,some (fanBlockRows 1282)),(3542,some (fanBlockRows 1283)),(3543,some (fanBlockRows 1284)),(3544,some (fanBlockRows 1285)),(3545,some (fanBlockRows 1286)),(3546,some (fanBlockRows 1287)),(3547,some (fanBlockRows 1288)),(3548,some (fanBlockRows 1289)),(3549,some (fanBlockRows 1290)),(3550,some (fanBlockRows 1291)),(3551,some (fanBlockRows 1292)),(3552,some (fanBlockRows 1293)),(3553,some (fanBlockRows 1294)),(3554,none),(3555,none),(3556,none),(3557,none),(3558,none),(3559,some (fanBlockRows 1295)),(3560,some (fanBlockRows 1296)),(3561,some (fanBlockRows 1297)),(3562,some (fanBlockRows 1298)),(3563,some (fanBlockRows 1299)),(3564,some (fanBlockRows 1300)),(3565,some (fanBlockRows 1301)),(3566,some (fanBlockRows 1302)),(3567,some (fanBlockRows 1303)),(3568,some (fanBlockRows 1304)),(3569,some (fanBlockRows 1305)),(3570,some (fanBlockRows 1306)),(3571,some (fanBlockRows 1307)),(3572,some (fanBlockRows 1308)),(3573,some (fanBlockRows 59)),(3574,some (fanBlockRows 59)),(3575,some (fanBlockRows 59)),(3576,some (fanBlockRows 59)),(3577,some (fanBlockRows 59)),(3578,some (fanBlockRows 59)),(3579,some (fanBlockRows 59)),(3580,some (fanBlockRows 59)),(3581,some (fanBlockRows 59)),(3582,some (fanBlockRows 1309)),(3583,some (fanBlockRows 1310)),(3584,some (fanBlockRows 1311)),(3585,some (fanBlockRows 1312)),(3586,some (fanBlockRows 1313)),(3587,some (fanBlockRows 1314)),(3588,some (fanBlockRows 1315)),(3589,some (fanBlockRows 1316)),(3590,some (fanBlockRows 1317)),(3591,some (fanBlockRows 1318)),(3592,some (fanBlockRows 1319)),(3593,some (fanBlockRows 1320)),(3594,some (fanBlockRows 1321)),(3595,some (fanBlockRows 1322)),(3596,some (fanBlockRows 1323)),(3597,some (fanBlockRows 1324)),(3598,some (fanBlockRows 1325)),(3599,some (fanBlockRows 1327)),(3600,some (fanBlockRows 1328)),(3601,some (fanBlockRows 1329)),(3602,some (fanBlockRows 1330)),(3603,some (fanBlockRows 1331)),(3604,some (fanBlockRows 1332)),(3605,some (fanBlockRows 1333)),(3606,some (fanBlockRows 1334)),(3607,some (fanBlockRows 1335)),(3608,some (fanBlockRows 1336)),(3609,some (fanBlockRows 1338)),(3610,some (fanBlockRows 1339)),(3611,some (fanBlockRows 1340)),(3612,some (fanBlockRows 1341)),(3613,some (fanBlockRows 1342)),(3614,some (fanBlockRows 1343)),(3615,some (fanBlockRows 1344)),(3616,some (fanBlockRows 1345)),(3617,some (fanBlockRows 1346)),(3618,some (fanBlockRows 1347)),(3619,some (fanBlockRows 1349)),(3620,some (fanBlockRows 1350)),(3621,some (fanBlockRows 1351)),(3622,some (fanBlockRows 1352)),(3623,some (fanBlockRows 1353)),(3624,some (fanBlockRows 1354)),(3625,some (fanBlockRows 1355)),(3626,some (fanBlockRows 1356)),(3627,some (fanBlockRows 1357)),(3628,some (fanBlockRows 1358)),(3629,some (fanBlockRows 1268)),(3630,some (fanBlockRows 1269)),(3631,some (fanBlockRows 1270)),(3632,some (fanBlockRows 1271)),(3633,some (fanBlockRows 1272)),(3634,some (fanBlockRows 1273)),(3635,some (fanBlockRows 1274)),(3636,some (fanBlockRows 1275)),(3637,some (fanBlockRows 1276)),(3638,some (fanBlockRows 1277)),(3639,some (fanBlockRows 1279)),(3640,some (fanBlockRows 1280)),(3641,none)]

theorem planHeaders_exact :
    N12Compact.C713DirectPruning.Step08.planHeaders = planHeaders := by rfl

theorem source_matches : ∀ plan ∈ planHeaders, SourceCheck sourceHeaders plan := by
  exact @of_decide_eq_true _ (List.decidableBAll _ planHeaders) (by decide +kernel)

theorem neighbors_exact :
    (List.finRange 94).map (fun j => (neighbors j).header.pose) = N12Compact.C713Shared.continuousScout713Domain5_4Ids := by
  decide +kernel

theorem neighbor_unblocked : ∀ j, (neighbors j).header.block = [] := by
  decide +kernel

theorem block_overlaps : N12Compact.C713DirectPruning.Step08.BlockOverlap := by
  change ∀ plan ∈ N12Compact.C713DirectPruning.Step08.planHeaders, HeaderOverlap dictionary N12Compact.C713Shared.continuousScout713Domain5_4Ids plan
  rw [planHeaders_exact]
  exact block_overlap_headers sources neighbors N12Compact.C713Shared.continuousScout713Domain5_4Ids
    sourceHeaders sourceHeaders_exact planHeaders source_matches
    neighbors_exact neighbor_unblocked pairs

#print axioms block_overlaps

end
end N12Compact.HistoricalCommon.C713.Step08
