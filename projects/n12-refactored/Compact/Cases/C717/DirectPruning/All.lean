import Compact.Cases.C717.DirectPruning.Step00
import Compact.Cases.C717.DirectPruning.Step01
import Compact.Cases.C717.DirectPruning.Step02
import Compact.Cases.C717.DirectPruning.Step03
import Compact.Cases.C717.DirectPruning.Step04
import Compact.Cases.C717.DirectPruning.Step05
import Compact.Cases.C717.DirectPruning.Step06
import Compact.Cases.C717.DirectPruning.Step07
import Compact.Cases.C717.DirectPruning.Step08
import Compact.Cases.C717.DirectPruning.Step09
import Compact.Cases.C717.DirectPruning.Step10
import Compact.Cases.C717.DirectPruning.Step11
import Compact.Cases.C717.DirectPruning.Step12
import Compact.Cases.C717.DirectPruning.Step13
import Compact.Cases.C717.DirectPruning.Step14
import Compact.Cases.C717.DirectPruning.Step15
import Compact.Cases.C717.DirectPruning.Step16
import Compact.Preservation.C717

namespace N12Compact.C717DirectPruning
open S12 S12Pilot IntegerSupport C713Shared
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

open N12Compact.Preservation.C717 S12Completion

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

/-- Only the unchanged original entrance and chord obligations. -/
structure Remaining : Prop where
  initial0 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain0_0 (p.square (ownerIndex p 1))
  initial1 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain1_0 (p.square (ownerIndex p 2))
  initial2 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain2_0 (p.square (ownerIndex p 12))
  initial3 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain3_0 (p.square (ownerIndex p 16))
  initial4 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain4_0 (p.square (ownerIndex p 32))
  initial6 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain6_0 (p.square (ownerIndex p 768))
  initial7 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain7_0 (p.square (ownerIndex p 3072))
  initial8 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain8_0 (p.square (ownerIndex p 4096))
  initial9 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain9_0 (p.square (ownerIndex p 8192))
  initial10 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain10_0 (p.square (ownerIndex p 16384))
  initial11 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout717Domain11_0 (p.square (ownerIndex p 32768))
  step17 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_8 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain0_15 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain11_0 (p.square (ownerIndex p 32768)) →
    OrientedPoseCovered continuousScout717Domain6_18 (p.square (ownerIndex p 768))
  step18 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout717Domain6_18 (p.square (ownerIndex p 768)) →
    OrientedPoseCovered continuousScout717Domain3_17 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout717Domain7_11 (p.square (ownerIndex p 3072)) →
    OrientedPoseCovered continuousScout717Domain9_13 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout717Domain6_19 (p.square (ownerIndex p 768))

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
    (remaining : Remaining) : N12Compact.Preservation.C717.Pending := by
  refine {
    initial0 := remaining.initial0
    initial1 := remaining.initial1
    initial2 := remaining.initial2
    initial3 := remaining.initial3
    initial4 := remaining.initial4
    initial6 := remaining.initial6
    initial7 := remaining.initial7
    initial8 := remaining.initial8
    initial9 := remaining.initial9
    initial10 := remaining.initial10
    initial11 := remaining.initial11
    step0 := by
      intro p hf incoming neighbors
      exact Step00.step_sound checked.step0
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 2)) incoming neighbors
        (owner_disjoint p hf 1 2
          (by decide +kernel) (by decide +kernel) (by decide))
    step1 := by
      intro p hf incoming neighbors
      exact Step01.step_sound checked.step1
        (p.square (ownerIndex p 2)) (p.square (ownerIndex p 4096)) incoming neighbors
        (owner_disjoint p hf 2 4096
          (by decide +kernel) (by decide +kernel) (by decide))
    step2 := by
      intro p hf incoming neighbors
      exact Step02.step_sound checked.step2
        (p.square (ownerIndex p 12)) (p.square (ownerIndex p 16384)) incoming neighbors
        (owner_disjoint p hf 12 16384
          (by decide +kernel) (by decide +kernel) (by decide))
    step3 := by
      intro p hf incoming neighbors
      exact Step03.step_sound checked.step3
        (p.square (ownerIndex p 16)) (p.square (ownerIndex p 32)) incoming neighbors
        (owner_disjoint p hf 16 32
          (by decide +kernel) (by decide +kernel) (by decide))
    step4 := by
      intro p hf incoming neighbors
      exact Step04.step_sound checked.step4
        (p.square (ownerIndex p 32)) (p.square (ownerIndex p 16384)) incoming neighbors
        (owner_disjoint p hf 32 16384
          (by decide +kernel) (by decide +kernel) (by decide))
    step5 := by
      intro p hf incoming neighbors
      exact Step05.step_sound checked.step5
        (p.square (ownerIndex p 768)) (p.square (ownerIndex p 1)) incoming neighbors
        (owner_disjoint p hf 768 1
          (by decide +kernel) (by decide +kernel) (by decide))
    step6 := by
      intro p hf incoming neighbors
      exact Step06.step_sound checked.step6
        (p.square (ownerIndex p 768)) (p.square (ownerIndex p 3072)) incoming neighbors
        (owner_disjoint p hf 768 3072
          (by decide +kernel) (by decide +kernel) (by decide))
    step7 := by
      intro p hf incoming neighbors
      exact Step07.step_sound checked.step7
        (p.square (ownerIndex p 768)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 768 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step8 := by
      intro p hf incoming neighbors
      exact Step08.step_sound checked.step8
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 16)) incoming neighbors
        (owner_disjoint p hf 3072 16
          (by decide +kernel) (by decide +kernel) (by decide))
    step9 := by
      intro p hf incoming neighbors
      exact Step09.step_sound checked.step9
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 768)) incoming neighbors
        (owner_disjoint p hf 3072 768
          (by decide +kernel) (by decide +kernel) (by decide))
    step10 := by
      intro p hf incoming neighbors
      exact Step10.step_sound checked.step10
        (p.square (ownerIndex p 3072)) (p.square (ownerIndex p 32768)) incoming neighbors
        (owner_disjoint p hf 3072 32768
          (by decide +kernel) (by decide +kernel) (by decide))
    step11 := by
      intro p hf incoming neighbors
      exact Step11.step_sound checked.step11
        (p.square (ownerIndex p 8192)) (p.square (ownerIndex p 12)) incoming neighbors
        (owner_disjoint p hf 8192 12
          (by decide +kernel) (by decide +kernel) (by decide))
    step12 := by
      intro p hf incoming neighbors
      exact Step12.step_sound checked.step12
        (p.square (ownerIndex p 8192)) (p.square (ownerIndex p 768)) incoming neighbors
        (owner_disjoint p hf 8192 768
          (by decide +kernel) (by decide +kernel) (by decide))
    step13 := by
      intro p hf incoming neighbors
      exact Step13.step_sound checked.step13
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 2)) incoming neighbors
        (owner_disjoint p hf 1 2
          (by decide +kernel) (by decide +kernel) (by decide))
    step14 := by
      intro p hf incoming neighbors
      exact Step14.step_sound checked.step14
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 1 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step15 := by
      intro p hf incoming neighbors
      exact Step15.step_sound checked.step15
        (p.square (ownerIndex p 16)) (p.square (ownerIndex p 32)) incoming neighbors
        (owner_disjoint p hf 16 32
          (by decide +kernel) (by decide +kernel) (by decide))
    step16 := by
      intro p hf incoming neighbors
      exact Step16.step_sound checked.step16
        (p.square (ownerIndex p 16)) (p.square (ownerIndex p 3072)) incoming neighbors
        (owner_disjoint p hf 16 3072
          (by decide +kernel) (by decide +kernel) (by decide))
    step17 := remaining.step17
    step18 := remaining.step18
  }

/-- Conditional original-case conclusion. No remaining overlap, entrance,
or chord field is declared true by this adapter. -/
theorem excludes_case_of_remaining (checked : BlockOverlaps) (remaining : Remaining) :
    ExcludesCase 717 :=
  N12Compact.Preservation.C717.excludes_case (pending_of_block_overlaps checked remaining)

#print axioms excludes_case_of_remaining

end
end N12Compact.C717DirectPruning
