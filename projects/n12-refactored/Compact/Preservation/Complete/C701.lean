import Compact.Cases.C701.DirectPruning.All
import Compact.HistoricalCommon.C701.Step00
import Compact.HistoricalCommon.C701.Step01
import Compact.HistoricalCommon.C701.Step02
import Compact.HistoricalCommon.C701.Step03
import Compact.HistoricalCommon.C701.Step04
import Compact.HistoricalCommon.C701.Step05
import Compact.HistoricalCommon.C701.Step07
import Compact.HistoricalCommon.C701.Step08
import Compact.HistoricalCommon.C701.Step09
import Compact.HistoricalCommon.C701.Step10
import Compact.HistoricalCommon.C701.Step11
import Compact.HistoricalCommon.C701.Step12
import Compact.HistoricalCommon.C701.Step13
import Compact.HistoricalCommon.C701.Step15
import Compact.HistoricalCommon.C701.Step16
import Compact.HistoricalCommon.C701.Step17
import Compact.HistoricalCommon.C701.Step18
import Compact.HistoricalCommon.C701.Step19
import Compact.HistoricalCommon.C701.Step21
import Compact.HistoricalCommon.C701.Step22
import Compact.HistoricalCommon.C701.Step24
import Compact.HistoricalCommon.C701.Step25
import Compact.HistoricalCommon.C701.Step26
import Compact.HistoricalCommon.C701.Step27
import Compact.HistoricalCommon.C701.Step29
import Compact.HistoricalCommon.C701.Step30
import Compact.Cases.C701.RecipeInitial.Entry
import Compact.Preservation.Chords.C701Step06
import Compact.Preservation.Chords.C701Step14
import Compact.Preservation.Chords.C701Step20
import Compact.Preservation.Chords.C701Step23
import Compact.Preservation.Chords.C701Step28

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace N12Compact.Preservation.Complete.C701
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C701DirectPruning.BlockOverlaps :=
  {
    step0 := HistoricalCommon.C701.Step00.block_overlaps
    step1 := HistoricalCommon.C701.Step01.block_overlaps
    step2 := HistoricalCommon.C701.Step02.block_overlaps
    step3 := HistoricalCommon.C701.Step03.block_overlaps
    step4 := HistoricalCommon.C701.Step04.block_overlaps
    step5 := HistoricalCommon.C701.Step05.block_overlaps
    step7 := HistoricalCommon.C701.Step07.block_overlaps
    step8 := HistoricalCommon.C701.Step08.block_overlaps
    step9 := HistoricalCommon.C701.Step09.block_overlaps
    step10 := HistoricalCommon.C701.Step10.block_overlaps
    step11 := HistoricalCommon.C701.Step11.block_overlaps
    step12 := HistoricalCommon.C701.Step12.block_overlaps
    step13 := HistoricalCommon.C701.Step13.block_overlaps
    step15 := HistoricalCommon.C701.Step15.block_overlaps
    step16 := HistoricalCommon.C701.Step16.block_overlaps
    step17 := HistoricalCommon.C701.Step17.block_overlaps
    step18 := HistoricalCommon.C701.Step18.block_overlaps
    step19 := HistoricalCommon.C701.Step19.block_overlaps
    step21 := HistoricalCommon.C701.Step21.block_overlaps
    step22 := HistoricalCommon.C701.Step22.block_overlaps
    step24 := HistoricalCommon.C701.Step24.block_overlaps
    step25 := HistoricalCommon.C701.Step25.block_overlaps
    step26 := HistoricalCommon.C701.Step26.block_overlaps
    step27 := HistoricalCommon.C701.Step27.block_overlaps
    step29 := HistoricalCommon.C701.Step29.block_overlaps
    step30 := HistoricalCommon.C701.Step30.block_overlaps
  }

private theorem remaining : C701DirectPruning.Remaining :=
  {
    initial0 := C701Entry.owner0_cover
    initial1 := C701Entry.owner1_cover
    initial2 := C701Entry.owner2_cover
    initial3 := C701Entry.owner3_cover
    initial4 := C701Entry.owner4_cover
    initial5 := C701Entry.owner5_cover
    initial6 := C701Entry.owner6_cover
    initial7 := C701Entry.owner7_cover
    initial8 := C701Entry.owner8_cover
    initial9 := C701Entry.owner9_cover
    initial10 := C701Entry.owner10_cover
    initial11 := C701Entry.owner11_cover
    step6 := Preservation.Chords.C701Step06.packing_sound
    step14 := Preservation.Chords.C701Step14.packing_sound
    step20 := Preservation.Chords.C701Step20.packing_sound
    step23 := Preservation.Chords.C701Step23.packing_sound
    step28 := Preservation.Chords.C701Step28.packing_sound
  }

theorem excludes_case : ExcludesCase 701 :=
  C701DirectPruning.excludes_case_of_remaining overlaps remaining

#print axioms excludes_case

end
end N12Compact.Preservation.Complete.C701
