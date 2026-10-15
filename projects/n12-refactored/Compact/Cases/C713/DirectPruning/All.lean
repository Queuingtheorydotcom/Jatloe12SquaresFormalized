import Compact.Cases.C713.DirectPruning.Step00
import Compact.Cases.C713.DirectPruning.Step01
import Compact.Cases.C713.DirectPruning.Step02
import Compact.Cases.C713.DirectPruning.Step03
import Compact.Cases.C713.DirectPruning.Step04
import Compact.Cases.C713.DirectPruning.Step06
import Compact.Cases.C713.DirectPruning.Step07
import Compact.Cases.C713.DirectPruning.Step08
import Compact.Cases.C713.DirectPruning.Step09
import Compact.Cases.C713.Assembly

namespace N12Compact.C713DirectPruning
open S12 S12Pilot IntegerSupport C713Shared
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

/-- Exactly the nine original pair-block overlap families remain. -/
structure BlockOverlaps : Prop where
  step0 : Step00.BlockOverlap
  step1 : Step01.BlockOverlap
  step2 : Step02.BlockOverlap
  step3 : Step03.BlockOverlap
  step4 : Step04.BlockOverlap
  step6 : Step06.BlockOverlap
  step7 : Step07.BlockOverlap
  step8 : Step08.BlockOverlap
  step9 : Step09.BlockOverlap

theorem pair_stages (checked : BlockOverlaps) : C713Assembly.PairStages :=
  {
    step0 := Step00.step_sound checked.step0
    step1 := Step01.step_sound checked.step1
    step2 := Step02.step_sound checked.step2
    step3 := Step03.step_sound checked.step3
    step4 := Step04.step_sound checked.step4
    step6 := Step06.step_sound checked.step6
    step7 := Step07.step_sound checked.step7
    step8 := Step08.step_sound checked.step8
    step9 := Step09.step_sound checked.step9
  }

/-- Conditional original-packing conclusion. This does not supply the
remaining block-overlap fields or assert an unconditional case exclusion. -/
theorem family_impossible_of_block_overlaps (checked : BlockOverlaps)
    (p : NormalizedPacking) (family : codedMarkerFamily p = case713Family) : False :=
  C713Assembly.family_impossible_of_pair_stages (pair_stages checked) p family

#print axioms family_impossible_of_block_overlaps

end
end N12Compact.C713DirectPruning
