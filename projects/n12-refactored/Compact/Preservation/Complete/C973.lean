import Compact.Cases.C973.DirectPruning.All
import Compact.HistoricalCommon.C973.Step00
import Compact.HistoricalCommon.C973.Step01
import Compact.HistoricalCommon.C973.Step02
import Compact.HistoricalCommon.C973.Step03
import Compact.HistoricalCommon.C973.Step04
import Compact.HistoricalCommon.C973.Step05
import Compact.HistoricalCommon.C973.Step06
import Compact.HistoricalCommon.C973.Step07
import Compact.HistoricalCommon.C973.Step08
import Compact.HistoricalCommon.C973.Step09
import Compact.HistoricalCommon.C973.Step12
import Compact.HistoricalCommon.C973.Step13
import Compact.HistoricalCommon.C973.Step14
import Compact.HistoricalCommon.C973.Step16
import Compact.HistoricalCommon.C973.Step17
import Compact.HistoricalCommon.C973.Step18
import Compact.HistoricalCommon.C973.Step19
import Compact.HistoricalCommon.C973.Step20
import Compact.HistoricalCommon.C973.Step21
import Compact.HistoricalCommon.C973.Step22
import Compact.HistoricalCommon.C973.Step23
import Compact.HistoricalCommon.C973.Step24
import Compact.HistoricalCommon.C973.Step27
import Compact.Cases.C973.RecipeInitial.Entry
import Compact.Preservation.Chords.C973Step10
import Compact.Preservation.Chords.C973Step11
import Compact.Preservation.Chords.C973Step15
import Compact.Preservation.Chords.C973Step25
import Compact.Preservation.Chords.C973Step26

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace N12Compact.Preservation.Complete.C973
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C973DirectPruning.BlockOverlaps :=
  {
    step0 := HistoricalCommon.C973.Step00.block_overlaps
    step1 := HistoricalCommon.C973.Step01.block_overlaps
    step2 := HistoricalCommon.C973.Step02.block_overlaps
    step3 := HistoricalCommon.C973.Step03.block_overlaps
    step4 := HistoricalCommon.C973.Step04.block_overlaps
    step5 := HistoricalCommon.C973.Step05.block_overlaps
    step6 := HistoricalCommon.C973.Step06.block_overlaps
    step7 := HistoricalCommon.C973.Step07.block_overlaps
    step8 := HistoricalCommon.C973.Step08.block_overlaps
    step9 := HistoricalCommon.C973.Step09.block_overlaps
    step12 := HistoricalCommon.C973.Step12.block_overlaps
    step13 := HistoricalCommon.C973.Step13.block_overlaps
    step14 := HistoricalCommon.C973.Step14.block_overlaps
    step16 := HistoricalCommon.C973.Step16.block_overlaps
    step17 := HistoricalCommon.C973.Step17.block_overlaps
    step18 := HistoricalCommon.C973.Step18.block_overlaps
    step19 := HistoricalCommon.C973.Step19.block_overlaps
    step20 := HistoricalCommon.C973.Step20.block_overlaps
    step21 := HistoricalCommon.C973.Step21.block_overlaps
    step22 := HistoricalCommon.C973.Step22.block_overlaps
    step23 := HistoricalCommon.C973.Step23.block_overlaps
    step24 := HistoricalCommon.C973.Step24.block_overlaps
    step27 := HistoricalCommon.C973.Step27.block_overlaps
  }

private theorem remaining : C973DirectPruning.Remaining :=
  {
    initial0 := C973Entry.owner0_cover
    initial1 := C973Entry.owner1_cover
    initial3 := C973Entry.owner3_cover
    initial4 := C973Entry.owner4_cover
    initial5 := C973Entry.owner5_cover
    initial6 := C973Entry.owner6_cover
    initial7 := C973Entry.owner7_cover
    initial8 := C973Entry.owner8_cover
    initial9 := C973Entry.owner9_cover
    initial10 := C973Entry.owner10_cover
    initial11 := C973Entry.owner11_cover
    step10 := Preservation.Chords.C973Step10.packing_sound
    step11 := Preservation.Chords.C973Step11.packing_sound
    step15 := Preservation.Chords.C973Step15.packing_sound
    step25 := Preservation.Chords.C973Step25.packing_sound
    step26 := Preservation.Chords.C973Step26.packing_sound
  }

theorem excludes_case : ExcludesCase 973 :=
  C973DirectPruning.excludes_case_of_remaining overlaps remaining

#print axioms excludes_case

end
end N12Compact.Preservation.Complete.C973
