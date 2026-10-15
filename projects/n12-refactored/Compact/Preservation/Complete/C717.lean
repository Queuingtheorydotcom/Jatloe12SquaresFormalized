import Compact.Cases.C717.DirectPruning.All
import Compact.HistoricalCommon.C717.Step00
import Compact.HistoricalCommon.C717.Step01
import Compact.HistoricalCommon.C717.Step02
import Compact.HistoricalCommon.C717.Step03
import Compact.HistoricalCommon.C717.Step04
import Compact.HistoricalCommon.C717.Step05
import Compact.HistoricalCommon.C717.Step06
import Compact.HistoricalCommon.C717.Step07
import Compact.HistoricalCommon.C717.Step08
import Compact.HistoricalCommon.C717.Step09
import Compact.HistoricalCommon.C717.Step10
import Compact.HistoricalCommon.C717.Step11
import Compact.HistoricalCommon.C717.Step12
import Compact.HistoricalCommon.C717.Step13
import Compact.HistoricalCommon.C717.Step14
import Compact.HistoricalCommon.C717.Step15
import Compact.HistoricalCommon.C717.Step16
import Compact.Cases.C717.RecipeInitial.Entry
import Compact.Preservation.Chords.C717Step17
import Compact.Preservation.Chords.C717Step18

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace N12Compact.Preservation.Complete.C717
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C717DirectPruning.BlockOverlaps :=
  {
    step0 := HistoricalCommon.C717.Step00.block_overlaps
    step1 := HistoricalCommon.C717.Step01.block_overlaps
    step2 := HistoricalCommon.C717.Step02.block_overlaps
    step3 := HistoricalCommon.C717.Step03.block_overlaps
    step4 := HistoricalCommon.C717.Step04.block_overlaps
    step5 := HistoricalCommon.C717.Step05.block_overlaps
    step6 := HistoricalCommon.C717.Step06.block_overlaps
    step7 := HistoricalCommon.C717.Step07.block_overlaps
    step8 := HistoricalCommon.C717.Step08.block_overlaps
    step9 := HistoricalCommon.C717.Step09.block_overlaps
    step10 := HistoricalCommon.C717.Step10.block_overlaps
    step11 := HistoricalCommon.C717.Step11.block_overlaps
    step12 := HistoricalCommon.C717.Step12.block_overlaps
    step13 := HistoricalCommon.C717.Step13.block_overlaps
    step14 := HistoricalCommon.C717.Step14.block_overlaps
    step15 := HistoricalCommon.C717.Step15.block_overlaps
    step16 := HistoricalCommon.C717.Step16.block_overlaps
  }

private theorem remaining : C717DirectPruning.Remaining :=
  {
    initial0 := C717Entry.owner0_cover
    initial1 := C717Entry.owner1_cover
    initial2 := C717Entry.owner2_cover
    initial3 := C717Entry.owner3_cover
    initial4 := C717Entry.owner4_cover
    initial6 := C717Entry.owner6_cover
    initial7 := C717Entry.owner7_cover
    initial8 := C717Entry.owner8_cover
    initial9 := C717Entry.owner9_cover
    initial10 := C717Entry.owner10_cover
    initial11 := C717Entry.owner11_cover
    step17 := Preservation.Chords.C717Step17.packing_sound
    step18 := Preservation.Chords.C717Step18.packing_sound
  }

theorem excludes_case : ExcludesCase 717 :=
  C717DirectPruning.excludes_case_of_remaining overlaps remaining

#print axioms excludes_case

end
end N12Compact.Preservation.Complete.C717
