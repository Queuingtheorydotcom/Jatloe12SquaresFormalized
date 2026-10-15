import Compact.Cases.C978.DirectPruning.All
import Compact.HistoricalCommon.C978.Step00
import Compact.HistoricalCommon.C978.Step01
import Compact.HistoricalCommon.C978.Step02
import Compact.HistoricalCommon.C978.Step03
import Compact.HistoricalCommon.C978.Step04
import Compact.HistoricalCommon.C978.Step05
import Compact.HistoricalCommon.C978.Step06
import Compact.HistoricalCommon.C978.Step07
import Compact.HistoricalCommon.C978.Step08
import Compact.HistoricalCommon.C978.Step09
import Compact.HistoricalCommon.C978.Step10
import Compact.HistoricalCommon.C978.Step12
import Compact.HistoricalCommon.C978.Step14
import Compact.HistoricalCommon.C978.Step15
import Compact.Cases.C978.RecipeInitial.Entry
import Compact.Preservation.Chords.C978Step11
import Compact.Preservation.Chords.C978Step13

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace N12Compact.Preservation.Complete.C978
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C978DirectPruning.BlockOverlaps :=
  {
    step0 := HistoricalCommon.C978.Step00.block_overlaps
    step1 := HistoricalCommon.C978.Step01.block_overlaps
    step2 := HistoricalCommon.C978.Step02.block_overlaps
    step3 := HistoricalCommon.C978.Step03.block_overlaps
    step4 := HistoricalCommon.C978.Step04.block_overlaps
    step5 := HistoricalCommon.C978.Step05.block_overlaps
    step6 := HistoricalCommon.C978.Step06.block_overlaps
    step7 := HistoricalCommon.C978.Step07.block_overlaps
    step8 := HistoricalCommon.C978.Step08.block_overlaps
    step9 := HistoricalCommon.C978.Step09.block_overlaps
    step10 := HistoricalCommon.C978.Step10.block_overlaps
    step12 := HistoricalCommon.C978.Step12.block_overlaps
    step14 := HistoricalCommon.C978.Step14.block_overlaps
    step15 := HistoricalCommon.C978.Step15.block_overlaps
  }

private theorem remaining : C978DirectPruning.Remaining :=
  {
    initial0 := C978Entry.owner0_cover
    initial1 := C978Entry.owner1_cover
    initial5 := C978Entry.owner5_cover
    initial6 := C978Entry.owner6_cover
    initial7 := C978Entry.owner7_cover
    initial8 := C978Entry.owner8_cover
    initial9 := C978Entry.owner9_cover
    initial10 := C978Entry.owner10_cover
    initial11 := C978Entry.owner11_cover
    step11 := Preservation.Chords.C978Step11.packing_sound
    step13 := Preservation.Chords.C978Step13.packing_sound
  }

theorem excludes_case : ExcludesCase 978 :=
  C978DirectPruning.excludes_case_of_remaining overlaps remaining

#print axioms excludes_case

end
end N12Compact.Preservation.Complete.C978
