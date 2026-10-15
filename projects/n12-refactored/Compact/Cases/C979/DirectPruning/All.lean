import Compact.Cases.C979.DirectPruning.Step00
import Compact.Cases.C979.DirectPruning.Step01
import Compact.Cases.C979.DirectPruning.Step02
import Compact.Cases.C979.DirectPruning.Step03
import Compact.Cases.C979.DirectPruning.Step04
import Compact.Cases.C979.DirectPruning.Step05
import Compact.Cases.C979.DirectPruning.Step06
import Compact.Cases.C979.DirectPruning.Step07
import Compact.Cases.C979.DirectPruning.Step08
import Compact.Cases.C979.DirectPruning.Step09
import Compact.Cases.C979.DirectPruning.Step10
import Compact.Cases.C979.DirectPruning.Step11
import Compact.Cases.C979.DirectPruning.Step12
import Compact.Cases.C979.DirectPruning.Step13
import Compact.Cases.C979.DirectPruning.Step14
import Compact.Cases.C979.DirectPruning.Step15
import Compact.Cases.C979.DirectPruning.Step16
import Compact.Cases.C979.DirectPruning.Step18
import Compact.Cases.C979.DirectPruning.Step19
import Compact.Cases.C979.DirectPruning.Step22
import Compact.Cases.C979.DirectPruning.Step23
import Compact.Cases.C979.DirectPruning.Step25
import Compact.Cases.C979.DirectPruning.Step26
import Compact.Cases.C979.DirectPruning.Step29
import Compact.Preservation.C979

namespace N12Compact.C979DirectPruning
open S12 S12Pilot IntegerSupport C713Shared
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

open N12Compact.Preservation.C979 S12Completion

structure BlockOverlaps : Prop where
  step0 : Step00.BlockOverlap
  step1 : Step01.BlockOverlap
  step2 : Step02.BlockOverlap
  step3 : Step03.BlockOverlap
  step4 : Step04.BlockOverlap
  step5 : Step05.BlockOverlap
  step6 : Step06.BlockOverlap
  step7 : Step07.BlockOverlap
  step8 : Step08.BlockOverlap
  step9 : Step09.BlockOverlap
  step10 : Step10.BlockOverlap
  step11 : Step11.BlockOverlap
  step12 : Step12.BlockOverlap
  step13 : Step13.BlockOverlap
  step14 : Step14.BlockOverlap
  step15 : Step15.BlockOverlap
  step16 : Step16.BlockOverlap
  step18 : Step18.BlockOverlap
  step19 : Step19.BlockOverlap
  step22 : Step22.BlockOverlap
  step23 : Step23.BlockOverlap
  step25 : Step25.BlockOverlap
  step26 : Step26.BlockOverlap
  step29 : Step29.BlockOverlap

/-- Only the unchanged original entrance and chord obligations. -/
structure Remaining : Prop where
  initial0 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain0_0 (p.square (ownerIndex p 1))
  initial1 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain1_0 (p.square (ownerIndex p 2))
  initial2 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain2_0 (p.square (ownerIndex p 12))
  initial3 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain3_0 (p.square (ownerIndex p 48))
  initial4 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain4_0 (p.square (ownerIndex p 192))
  initial5 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain5_0 (p.square (ownerIndex p 256))
  initial6 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain6_0 (p.square (ownerIndex p 512))
  initial7 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain7_0 (p.square (ownerIndex p 3072))
  initial8 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain8_0 (p.square (ownerIndex p 4096))
  initial9 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain9_0 (p.square (ownerIndex p 8192))
  initial10 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain10_0 (p.square (ownerIndex p 16384))
  initial11 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout979Domain11_0 (p.square (ownerIndex p 32768))
  step17 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout979Domain11_7 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout979Domain0_9 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout979Domain5_10 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout979Domain7_16 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout979Domain11_18 (p.square (ownerIndex p 32768))
  step20 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout979Domain6_13 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout979Domain2_2 (p.square (ownerIndex p 12)) →
    OrientedPoseCovered continuousScout979Domain3_20 (p.square (ownerIndex p 48)) →
    OrientedPoseCovered continuousScout979Domain10_0 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout979Domain6_21 (p.square (ownerIndex p 512))
  step21 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout979Domain6_21 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout979Domain7_16 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout979Domain9_17 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout979Domain11_19 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout979Domain6_22 (p.square (ownerIndex p 512))
  step24 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout979Domain7_16 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout979Domain6_24 (p.square (ownerIndex p 512)) →
    OrientedPoseCovered continuousScout979Domain9_17 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout979Domain11_19 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout979Domain7_25 (p.square (ownerIndex p 3072))
  step27 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout979Domain4_4 (p.square (ownerIndex p 192)) →
    OrientedPoseCovered continuousScout979Domain0_27 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout979Domain1_1 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout979Domain8_0 (p.square (ownerIndex p 4096)) →
    OrientedPoseCovered continuousScout979Domain4_28 (p.square (ownerIndex p 192))
  step28 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout979Domain4_28 (p.square (ownerIndex p 192)) →
    OrientedPoseCovered continuousScout979Domain0_27 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout979Domain5_10 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout979Domain7_25 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout979Domain4_29 (p.square (ownerIndex p 192))

private theorem owner_disjoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (a b : Nat)
    (ha : a ∈ family) (hb : b ∈ family) (distinct : a ≠ b) :
    ∀ x y, ¬((p.square (ownerIndex p a)).Inside x y ∧
      (p.square (ownerIndex p b)).Inside x y) := by
  apply p.disjoint
  intro equal
  apply distinct
  have left := ownerIndex_spec p a (by rw [hf]; exact ha)
  have right := ownerIndex_spec p b (by rw [hf]; exact hb)
  exact left.symm.trans ((congrArg (markerCode p) equal).trans right)

theorem pending_of_block_overlaps (checked : BlockOverlaps)
    (remaining : Remaining) : N12Compact.Preservation.C979.Pending := by
  refine {
    initial0 := remaining.initial0
    initial1 := remaining.initial1
    initial2 := remaining.initial2
    initial3 := remaining.initial3
    initial4 := remaining.initial4
    initial5 := remaining.initial5
    initial6 := remaining.initial6
    initial7 := remaining.initial7
    initial8 := remaining.initial8
    initial9 := remaining.initial9
    initial10 := remaining.initial10
    initial11 := remaining.initial11
    step0 := by
      intro p hf incoming neighbors
      exact Step00.step_sound checked.step0
        (p.square (ownerIndex p 2)) (p.square (ownerIndex p 4096)) incoming neighbors
        (owner_disjoint p hf 2 4096
          (by decide +kernel) (by decide +kernel) (by decide))
    step1 := by
      intro p hf incoming neighbors
      exact Step01.step_sound checked.step1
        (p.square (ownerIndex p 12)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 12 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step2 := by
      intro p hf incoming neighbors
      exact Step02.step_sound checked.step2
        (p.square (ownerIndex p 48)) (p.square (ownerIndex p 16384)) incoming neighbors
        (owner_disjoint p hf 48 16384
          (by decide +kernel) (by decide +kernel) (by decide))
    step3 := by
      intro p hf incoming neighbors
      exact Step03.step_sound checked.step3
        (p.square (ownerIndex p 192)) (p.square (ownerIndex p 4096)) incoming neighbors
        (owner_disjoint p hf 192 4096
          (by decide +kernel) (by decide +kernel) (by decide))
    step4 := by
      intro p hf incoming neighbors
      exact Step04.step_sound checked.step4
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 256)) incoming neighbors
        (owner_disjoint p hf 3072 256
          (by decide +kernel) (by decide +kernel) (by decide))
    step5 := by
      intro p hf incoming neighbors
      exact Step05.step_sound checked.step5
        (p.square (ownerIndex p 32768)) (p.square (ownerIndex p 48)) incoming neighbors
        (owner_disjoint p hf 32768 48
          (by decide +kernel) (by decide +kernel) (by decide))
    step6 := by
      intro p hf incoming neighbors
      exact Step06.step_sound checked.step6
        (p.square (ownerIndex p 32768)) (p.square (ownerIndex p 192)) incoming neighbors
        (owner_disjoint p hf 32768 192
          (by decide +kernel) (by decide +kernel) (by decide))
    step7 := by
      intro p hf incoming neighbors
      exact Step07.step_sound checked.step7
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 2)) incoming neighbors
        (owner_disjoint p hf 1 2
          (by decide +kernel) (by decide +kernel) (by decide))
    step8 := by
      intro p hf incoming neighbors
      exact Step08.step_sound checked.step8
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 1 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step9 := by
      intro p hf incoming neighbors
      exact Step09.step_sound checked.step9
        (p.square (ownerIndex p 256)) (p.square (ownerIndex p 1)) incoming neighbors
        (owner_disjoint p hf 256 1
          (by decide +kernel) (by decide +kernel) (by decide))
    step10 := by
      intro p hf incoming neighbors
      exact Step10.step_sound checked.step10
        (p.square (ownerIndex p 512)) (p.square (ownerIndex p 12)) incoming neighbors
        (owner_disjoint p hf 512 12
          (by decide +kernel) (by decide +kernel) (by decide))
    step11 := by
      intro p hf incoming neighbors
      exact Step11.step_sound checked.step11
        (p.square (ownerIndex p 512)) (p.square (ownerIndex p 3072)) incoming neighbors
        (owner_disjoint p hf 512 3072
          (by decide +kernel) (by decide +kernel) (by decide))
    step12 := by
      intro p hf incoming neighbors
      exact Step12.step_sound checked.step12
        (p.square (ownerIndex p 512)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 512 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step13 := by
      intro p hf incoming neighbors
      exact Step13.step_sound checked.step13
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 256)) incoming neighbors
        (owner_disjoint p hf 3072 256
          (by decide +kernel) (by decide +kernel) (by decide))
    step14 := by
      intro p hf incoming neighbors
      exact Step14.step_sound checked.step14
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 512)) incoming neighbors
        (owner_disjoint p hf 3072 512
          (by decide +kernel) (by decide +kernel) (by decide))
    step15 := by
      intro p hf incoming neighbors
      exact Step15.step_sound checked.step15
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 32768)) incoming neighbors
        (owner_disjoint p hf 3072 32768
          (by decide +kernel) (by decide +kernel) (by decide))
    step16 := by
      intro p hf incoming neighbors
      exact Step16.step_sound checked.step16
        (p.square (ownerIndex p 8192)) (p.square (ownerIndex p 512)) incoming neighbors
        (owner_disjoint p hf 8192 512
          (by decide +kernel) (by decide +kernel) (by decide))
    step17 := remaining.step17
    step18 := by
      intro p hf incoming neighbors
      exact Step18.step_sound checked.step18
        (p.square (ownerIndex p 32768)) (p.square (ownerIndex p 3072)) incoming neighbors
        (owner_disjoint p hf 32768 3072
          (by decide +kernel) (by decide +kernel) (by decide))
    step19 := by
      intro p hf incoming neighbors
      exact Step19.step_sound checked.step19
        (p.square (ownerIndex p 48)) (p.square (ownerIndex p 32768)) incoming neighbors
        (owner_disjoint p hf 48 32768
          (by decide +kernel) (by decide +kernel) (by decide))
    step20 := remaining.step20
    step21 := remaining.step21
    step22 := by
      intro p hf incoming neighbors
      exact Step22.step_sound checked.step22
        (p.square (ownerIndex p 512)) (p.square (ownerIndex p 3072)) incoming neighbors
        (owner_disjoint p hf 512 3072
          (by decide +kernel) (by decide +kernel) (by decide))
    step23 := by
      intro p hf incoming neighbors
      exact Step23.step_sound checked.step23
        (p.square (ownerIndex p 512)) (p.square (ownerIndex p 16384)) incoming neighbors
        (owner_disjoint p hf 512 16384
          (by decide +kernel) (by decide +kernel) (by decide))
    step24 := remaining.step24
    step25 := by
      intro p hf incoming neighbors
      exact Step25.step_sound checked.step25
        (p.square (ownerIndex p 8192)) (p.square (ownerIndex p 512)) incoming neighbors
        (owner_disjoint p hf 8192 512
          (by decide +kernel) (by decide +kernel) (by decide))
    step26 := by
      intro p hf incoming neighbors
      exact Step26.step_sound checked.step26
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 1 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step27 := remaining.step27
    step28 := remaining.step28
    step29 := by
      intro p hf incoming neighbors
      exact Step29.step_sound checked.step29
        (p.square (ownerIndex p 192)) (p.square (ownerIndex p 3072)) incoming neighbors
        (owner_disjoint p hf 192 3072
          (by decide +kernel) (by decide +kernel) (by decide))
  }

/-- Conditional original-case conclusion. No remaining overlap, entrance,
or chord field is declared true by this adapter. -/
theorem excludes_case_of_remaining (checked : BlockOverlaps) (remaining : Remaining) :
    ExcludesCase 979 :=
  N12Compact.Preservation.C979.excludes_case (pending_of_block_overlaps checked remaining)

#print axioms excludes_case_of_remaining

end
end N12Compact.C979DirectPruning
