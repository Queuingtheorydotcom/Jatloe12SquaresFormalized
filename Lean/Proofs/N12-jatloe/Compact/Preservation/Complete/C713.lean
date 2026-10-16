import Compact.Cases.C713.DirectPruning.All
import Compact.HistoricalCommon.C713.Step00
import Compact.HistoricalCommon.C713.Step01
import Compact.HistoricalCommon.C713.Step02
import Compact.HistoricalCommon.C713.Step03
import Compact.HistoricalCommon.C713.Step04
import Compact.HistoricalCommon.C713.Step06
import Compact.HistoricalCommon.C713.Step07
import Compact.HistoricalCommon.C713.Step08
import Compact.HistoricalCommon.C713.Step09
import Compact.Assembly.RowIdentity

/-! Exact original case composition. Acceptance requires all imported
numerical and original-packing adapters; this source contains no new premise. -/
namespace N12Compact.Preservation.Complete.C713
open S12 S12Pilot S12Completion
set_option Elab.async false
noncomputable section

private theorem overlaps : C713DirectPruning.BlockOverlaps :=
  {
    step0 := HistoricalCommon.C713.Step00.block_overlaps
    step1 := HistoricalCommon.C713.Step01.block_overlaps
    step2 := HistoricalCommon.C713.Step02.block_overlaps
    step3 := HistoricalCommon.C713.Step03.block_overlaps
    step4 := HistoricalCommon.C713.Step04.block_overlaps
    step6 := HistoricalCommon.C713.Step06.block_overlaps
    step7 := HistoricalCommon.C713.Step07.block_overlaps
    step8 := HistoricalCommon.C713.Step08.block_overlaps
    step9 := HistoricalCommon.C713.Step09.block_overlaps
  }

private theorem row_checked :
    (RowIdentity.rowAt 394).originalId = 713 ∧
    (RowIdentity.rowAt 394).groups = case713Family := by decide +kernel

theorem excludes_case : ExcludesCase 713 := by
  intro r hr hid p hf
  apply C713DirectPruning.family_impossible_of_block_overlaps overlaps p
  exact hf.trans (RowIdentity.family_at 394 713 case713Family row_checked r hr hid)

#print axioms excludes_case

end
end N12Compact.Preservation.Complete.C713
