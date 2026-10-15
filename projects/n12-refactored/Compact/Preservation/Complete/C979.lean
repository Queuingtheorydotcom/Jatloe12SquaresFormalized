import Compact.Cases.C979.DirectPruning.All
import Compact.HistoricalCommon.C979.Step00
import Compact.HistoricalCommon.C979.Step01
import Compact.HistoricalCommon.C979.Step02
import Compact.HistoricalCommon.C979.Step03
import Compact.HistoricalCommon.C979.Step04
import Compact.HistoricalCommon.C979.Step05
import Compact.HistoricalCommon.C979.Step06
import Compact.HistoricalCommon.C979.Step07
import Compact.HistoricalCommon.C979.Step08
import Compact.HistoricalCommon.C979.Step09
import Compact.HistoricalCommon.C979.Step10
import Compact.HistoricalCommon.C979.Step11
import Compact.HistoricalCommon.C979.Step12
import Compact.HistoricalCommon.C979.Step13
import Compact.HistoricalCommon.C979.Step14
import Compact.HistoricalCommon.C979.Step15
import Compact.HistoricalCommon.C979.Step16
import Compact.HistoricalCommon.C979.Step18
import Compact.HistoricalCommon.C979.Step19
import Compact.HistoricalCommon.C979.Step22
import Compact.HistoricalCommon.C979.Step23
import Compact.HistoricalCommon.C979.Step25
import Compact.HistoricalCommon.C979.Step26
import Compact.HistoricalCommon.C979.Step29
import Compact.Cases.C979.RecipeInitial.Entry
import Compact.Preservation.Chords.C979Step17
import Compact.Preservation.Chords.C979Step20
import Compact.Preservation.Chords.C979Step21
import Compact.Preservation.Chords.C979Step24
import Compact.Preservation.Chords.C979Step27
import Compact.Preservation.Chords.C979Step28

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace N12Compact.Preservation.Complete.C979
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C979DirectPruning.BlockOverlaps :=
  {
    step0 := HistoricalCommon.C979.Step00.block_overlaps
    step1 := HistoricalCommon.C979.Step01.block_overlaps
    step2 := HistoricalCommon.C979.Step02.block_overlaps
    step3 := HistoricalCommon.C979.Step03.block_overlaps
    step4 := HistoricalCommon.C979.Step04.block_overlaps
    step5 := HistoricalCommon.C979.Step05.block_overlaps
    step6 := HistoricalCommon.C979.Step06.block_overlaps
    step7 := HistoricalCommon.C979.Step07.block_overlaps
    step8 := HistoricalCommon.C979.Step08.block_overlaps
    step9 := HistoricalCommon.C979.Step09.block_overlaps
    step10 := HistoricalCommon.C979.Step10.block_overlaps
    step11 := HistoricalCommon.C979.Step11.block_overlaps
    step12 := HistoricalCommon.C979.Step12.block_overlaps
    step13 := HistoricalCommon.C979.Step13.block_overlaps
    step14 := HistoricalCommon.C979.Step14.block_overlaps
    step15 := HistoricalCommon.C979.Step15.block_overlaps
    step16 := HistoricalCommon.C979.Step16.block_overlaps
    step18 := HistoricalCommon.C979.Step18.block_overlaps
    step19 := HistoricalCommon.C979.Step19.block_overlaps
    step22 := HistoricalCommon.C979.Step22.block_overlaps
    step23 := HistoricalCommon.C979.Step23.block_overlaps
    step25 := HistoricalCommon.C979.Step25.block_overlaps
    step26 := HistoricalCommon.C979.Step26.block_overlaps
    step29 := HistoricalCommon.C979.Step29.block_overlaps
  }

private theorem remaining : C979DirectPruning.Remaining :=
  {
    initial0 := C979Entry.owner0_cover
    initial1 := C979Entry.owner1_cover
    initial2 := C979Entry.owner2_cover
    initial3 := C979Entry.owner3_cover
    initial4 := C979Entry.owner4_cover
    initial5 := C979Entry.owner5_cover
    initial6 := C979Entry.owner6_cover
    initial7 := C979Entry.owner7_cover
    initial8 := C979Entry.owner8_cover
    initial9 := C979Entry.owner9_cover
    initial10 := C979Entry.owner10_cover
    initial11 := C979Entry.owner11_cover
    step17 := Preservation.Chords.C979Step17.packing_sound
    step20 := Preservation.Chords.C979Step20.packing_sound
    step21 := Preservation.Chords.C979Step21.packing_sound
    step24 := Preservation.Chords.C979Step24.packing_sound
    step27 := Preservation.Chords.C979Step27.packing_sound
    step28 := Preservation.Chords.C979Step28.packing_sound
  }

theorem excludes_case : ExcludesCase 979 :=
  C979DirectPruning.excludes_case_of_remaining overlaps remaining

#print axioms excludes_case

end
end N12Compact.Preservation.Complete.C979
