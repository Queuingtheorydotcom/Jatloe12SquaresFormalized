import Compact.Cases.C713.HeightData.Batch00
import Compact.Cases.C713.HeightData.Batch01
import Compact.Cases.C713.HeightData.Batch02
import Compact.Cases.C713.HeightData.Batch03
import Compact.Cases.C713.HeightData.Batch04
import Compact.Cases.C713.HeightData.Batch05
import Compact.Cases.C713.HeightData.Batch06
import Compact.Cases.C713.HeightData.Batch07
import Compact.Cases.C713.HeightData.Batch08
import Compact.Cases.C713.HeightData.Batch09
import Compact.Cases.C713.HeightData.Batch10
import Compact.Cases.C713.HeightData.Batch11
import Compact.Cases.C713.HeightData.Batch12
import Compact.Cases.C713.HeightData.Batch13
import Compact.Cases.C713.SharedDomains

namespace N12Compact.C713HeightData
open S12 S12Pilot IntegerSupport C713Height VertexCutRelaxation
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def checkedRecords : Array {entry : Entry // entry.Check} := #[
  ⟨entry0,entry0_checked⟩,
  ⟨entry1,entry1_checked⟩,
  ⟨entry2,entry2_checked⟩,
  ⟨entry3,entry3_checked⟩,
  ⟨entry4,entry4_checked⟩,
  ⟨entry5,entry5_checked⟩,
  ⟨entry6,entry6_checked⟩,
  ⟨entry7,entry7_checked⟩,
  ⟨entry8,entry8_checked⟩,
  ⟨entry9,entry9_checked⟩,
  ⟨entry10,entry10_checked⟩,
  ⟨entry11,entry11_checked⟩,
  ⟨entry12,entry12_checked⟩,
  ⟨entry13,entry13_checked⟩,
  ⟨entry14,entry14_checked⟩,
  ⟨entry15,entry15_checked⟩,
  ⟨entry16,entry16_checked⟩,
  ⟨entry17,entry17_checked⟩,
  ⟨entry18,entry18_checked⟩,
  ⟨entry19,entry19_checked⟩,
  ⟨entry20,entry20_checked⟩,
  ⟨entry21,entry21_checked⟩,
  ⟨entry22,entry22_checked⟩,
  ⟨entry23,entry23_checked⟩,
  ⟨entry24,entry24_checked⟩,
  ⟨entry25,entry25_checked⟩,
  ⟨entry26,entry26_checked⟩,
  ⟨entry27,entry27_checked⟩,
  ⟨entry28,entry28_checked⟩,
  ⟨entry29,entry29_checked⟩,
  ⟨entry30,entry30_checked⟩,
  ⟨entry31,entry31_checked⟩,
  ⟨entry32,entry32_checked⟩,
  ⟨entry33,entry33_checked⟩,
  ⟨entry34,entry34_checked⟩,
  ⟨entry35,entry35_checked⟩,
  ⟨entry36,entry36_checked⟩,
  ⟨entry37,entry37_checked⟩,
  ⟨entry38,entry38_checked⟩,
  ⟨entry39,entry39_checked⟩,
  ⟨entry40,entry40_checked⟩,
  ⟨entry41,entry41_checked⟩,
  ⟨entry42,entry42_checked⟩,
  ⟨entry43,entry43_checked⟩,
  ⟨entry44,entry44_checked⟩,
  ⟨entry45,entry45_checked⟩,
  ⟨entry46,entry46_checked⟩,
  ⟨entry47,entry47_checked⟩,
  ⟨entry48,entry48_checked⟩,
  ⟨entry49,entry49_checked⟩,
  ⟨entry50,entry50_checked⟩,
  ⟨entry51,entry51_checked⟩,
  ⟨entry52,entry52_checked⟩,
  ⟨entry53,entry53_checked⟩,
  ⟨entry54,entry54_checked⟩,
  ⟨entry55,entry55_checked⟩,
  ⟨entry56,entry56_checked⟩,
  ⟨entry57,entry57_checked⟩,
  ⟨entry58,entry58_checked⟩,
  ⟨entry59,entry59_checked⟩,
  ⟨entry60,entry60_checked⟩,
  ⟨entry61,entry61_checked⟩,
  ⟨entry62,entry62_checked⟩,
  ⟨entry63,entry63_checked⟩,
  ⟨entry64,entry64_checked⟩,
  ⟨entry65,entry65_checked⟩,
  ⟨entry66,entry66_checked⟩,
  ⟨entry67,entry67_checked⟩,
  ⟨entry68,entry68_checked⟩,
  ⟨entry69,entry69_checked⟩,
  ⟨entry70,entry70_checked⟩,
  ⟨entry71,entry71_checked⟩,
  ⟨entry72,entry72_checked⟩,
  ⟨entry73,entry73_checked⟩,
  ⟨entry74,entry74_checked⟩,
  ⟨entry75,entry75_checked⟩,
  ⟨entry76,entry76_checked⟩,
  ⟨entry77,entry77_checked⟩,
  ⟨entry78,entry78_checked⟩,
  ⟨entry79,entry79_checked⟩,
  ⟨entry80,entry80_checked⟩,
  ⟨entry81,entry81_checked⟩,
  ⟨entry82,entry82_checked⟩,
  ⟨entry83,entry83_checked⟩,
  ⟨entry84,entry84_checked⟩,
  ⟨entry85,entry85_checked⟩,
  ⟨entry86,entry86_checked⟩,
  ⟨entry87,entry87_checked⟩,
  ⟨entry88,entry88_checked⟩,
  ⟨entry89,entry89_checked⟩,
  ⟨entry90,entry90_checked⟩,
  ⟨entry91,entry91_checked⟩,
  ⟨entry92,entry92_checked⟩,
  ⟨entry93,entry93_checked⟩,
  ⟨entry94,entry94_checked⟩,
  ⟨entry95,entry95_checked⟩,
  ⟨entry96,entry96_checked⟩,
  ⟨entry97,entry97_checked⟩,
  ⟨entry98,entry98_checked⟩,
  ⟨entry99,entry99_checked⟩,
  ⟨entry100,entry100_checked⟩,
  ⟨entry101,entry101_checked⟩,
  ⟨entry102,entry102_checked⟩,
  ⟨entry103,entry103_checked⟩,
  ⟨entry104,entry104_checked⟩,
  ⟨entry105,entry105_checked⟩,
  ⟨entry106,entry106_checked⟩,
  ⟨entry107,entry107_checked⟩]

def record (i : Fin 108) : Entry :=
  (checkedRecords[i.val]'(by change i.val < 108; exact i.isLt)).val

theorem record_checked (i : Fin 108) : (record i).Check :=
  (checkedRecords[i.val]'(by change i.val < 108; exact i.isLt)).property

theorem source_ids :
    (List.finRange 108).map (fun i => (record i).spec.source) =
      C713Shared.continuousScout713Domain7_0Ids := by rfl

theorem target_ids :
    (List.finRange 108).flatMap (fun i => (record i).spec.target.toList) =
      C713Shared.continuousScout713Domain7_6Ids := by rfl

#print axioms record_checked

end N12Compact.C713HeightData
