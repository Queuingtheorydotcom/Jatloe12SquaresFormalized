import Compact.Cases.C701.DirectPruning.Step00
import Compact.Cases.C701.DirectPruning.Step01
import Compact.Cases.C701.DirectPruning.Step02
import Compact.Cases.C701.DirectPruning.Step03
import Compact.Cases.C701.DirectPruning.Step04
import Compact.Cases.C701.DirectPruning.Step05
import Compact.Cases.C701.DirectPruning.Step07
import Compact.Cases.C701.DirectPruning.Step08
import Compact.Cases.C701.DirectPruning.Step09
import Compact.Cases.C701.DirectPruning.Step10
import Compact.Cases.C701.DirectPruning.Step11
import Compact.Cases.C701.DirectPruning.Step12
import Compact.Cases.C701.DirectPruning.Step13
import Compact.Cases.C701.DirectPruning.Step15
import Compact.Cases.C701.DirectPruning.Step16
import Compact.Cases.C701.DirectPruning.Step17
import Compact.Cases.C701.DirectPruning.Step18
import Compact.Cases.C701.DirectPruning.Step19
import Compact.Cases.C701.DirectPruning.Step21
import Compact.Cases.C701.DirectPruning.Step22
import Compact.Cases.C701.DirectPruning.Step24
import Compact.Cases.C701.DirectPruning.Step25
import Compact.Cases.C701.DirectPruning.Step26
import Compact.Cases.C701.DirectPruning.Step27
import Compact.Cases.C701.DirectPruning.Step29
import Compact.Cases.C701.DirectPruning.Step30
import Compact.Preservation.C701

namespace N12Compact.C701DirectPruning
open S12 S12Pilot IntegerSupport C713Shared
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

open N12Compact.Preservation.C701 S12Completion

structure BlockOverlaps : Prop where
  step0 : Step00.BlockOverlap
  step1 : Step01.BlockOverlap
  step2 : Step02.BlockOverlap
  step3 : Step03.BlockOverlap
  step4 : Step04.BlockOverlap
  step5 : Step05.BlockOverlap
  step7 : Step07.BlockOverlap
  step8 : Step08.BlockOverlap
  step9 : Step09.BlockOverlap
  step10 : Step10.BlockOverlap
  step11 : Step11.BlockOverlap
  step12 : Step12.BlockOverlap
  step13 : Step13.BlockOverlap
  step15 : Step15.BlockOverlap
  step16 : Step16.BlockOverlap
  step17 : Step17.BlockOverlap
  step18 : Step18.BlockOverlap
  step19 : Step19.BlockOverlap
  step21 : Step21.BlockOverlap
  step22 : Step22.BlockOverlap
  step24 : Step24.BlockOverlap
  step25 : Step25.BlockOverlap
  step26 : Step26.BlockOverlap
  step27 : Step27.BlockOverlap
  step29 : Step29.BlockOverlap
  step30 : Step30.BlockOverlap

/-- Only the unchanged original entrance and chord obligations. -/
structure Remaining : Prop where
  initial0 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain0_0 (p.square (ownerIndex p 1))
  initial1 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain1_0 (p.square (ownerIndex p 2))
  initial2 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain2_0 (p.square (ownerIndex p 12))
  initial3 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain3_0 (p.square (ownerIndex p 16))
  initial4 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain4_0 (p.square (ownerIndex p 32))
  initial5 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain5_0 (p.square (ownerIndex p 192))
  initial6 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain6_0 (p.square (ownerIndex p 256))
  initial7 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain7_0 (p.square (ownerIndex p 1536))
  initial8 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain8_0 (p.square (ownerIndex p 4096))
  initial9 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain9_0 (p.square (ownerIndex p 8192))
  initial10 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain10_0 (p.square (ownerIndex p 16384))
  initial11 : ∀ p : NormalizedPacking,
    codedMarkerFamily p = family → OrientedPoseCovered continuousScout701Domain11_0 (p.square (ownerIndex p 34816))
  step6 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout701Domain7_0 (p.square (ownerIndex p 1536)) →
    OrientedPoseCovered continuousScout701Domain1_3 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout701Domain6_0 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout701Domain7_7 (p.square (ownerIndex p 1536))
  step14 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout701Domain9_0 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout701Domain1_3 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout701Domain6_13 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout701Domain9_15 (p.square (ownerIndex p 8192))
  step20 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout701Domain1_3 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout701Domain0_20 (p.square (ownerIndex p 1)) →
    OrientedPoseCovered continuousScout701Domain2_5 (p.square (ownerIndex p 12)) →
    OrientedPoseCovered continuousScout701Domain9_17 (p.square (ownerIndex p 8192)) →
    OrientedPoseCovered continuousScout701Domain1_21 (p.square (ownerIndex p 2))
  step23 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout701Domain7_14 (p.square (ownerIndex p 1536)) →
    OrientedPoseCovered continuousScout701Domain1_22 (p.square (ownerIndex p 2)) →
    OrientedPoseCovered continuousScout701Domain6_13 (p.square (ownerIndex p 256)) →
    OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout701Domain7_24 (p.square (ownerIndex p 1536))
  step28 : ∀ p : NormalizedPacking, codedMarkerFamily p = family →
    OrientedPoseCovered continuousScout701Domain3_0 (p.square (ownerIndex p 16)) →
    OrientedPoseCovered continuousScout701Domain2_5 (p.square (ownerIndex p 12)) →
    OrientedPoseCovered continuousScout701Domain4_23 (p.square (ownerIndex p 32)) →
    OrientedPoseCovered continuousScout701Domain10_6 (p.square (ownerIndex p 16384)) →
    OrientedPoseCovered continuousScout701Domain3_29 (p.square (ownerIndex p 16))

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
    (remaining : Remaining) : N12Compact.Preservation.C701.Pending := by
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
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 1 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step1 := by
      intro p hf incoming neighbors
      exact Step01.step_sound checked.step1
        (p.square (ownerIndex p 2)) (p.square (ownerIndex p 1)) incoming neighbors
        (owner_disjoint p hf 2 1
          (by decide +kernel) (by decide +kernel) (by decide))
    step2 := by
      intro p hf incoming neighbors
      exact Step02.step_sound checked.step2
        (p.square (ownerIndex p 2)) (p.square (ownerIndex p 4096)) incoming neighbors
        (owner_disjoint p hf 2 4096
          (by decide +kernel) (by decide +kernel) (by decide))
    step3 := by
      intro p hf incoming neighbors
      exact Step03.step_sound checked.step3
        (p.square (ownerIndex p 12)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 12 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step4 := by
      intro p hf incoming neighbors
      exact Step04.step_sound checked.step4
        (p.square (ownerIndex p 12)) (p.square (ownerIndex p 16384)) incoming neighbors
        (owner_disjoint p hf 12 16384
          (by decide +kernel) (by decide +kernel) (by decide))
    step5 := by
      intro p hf incoming neighbors
      exact Step05.step_sound checked.step5
        (p.square (ownerIndex p 16384)) (p.square (ownerIndex p 12)) incoming neighbors
        (owner_disjoint p hf 16384 12
          (by decide +kernel) (by decide +kernel) (by decide))
    step6 := remaining.step6
    step7 := by
      intro p hf incoming neighbors
      exact Step07.step_sound checked.step7
        (p.square (ownerIndex p 1536)) (p.square (ownerIndex p 16384)) incoming neighbors
        (owner_disjoint p hf 1536 16384
          (by decide +kernel) (by decide +kernel) (by decide))
    step8 := by
      intro p hf incoming neighbors
      exact Step08.step_sound checked.step8
        (p.square (ownerIndex p 1536)) (p.square (ownerIndex p 34816)) incoming neighbors
        (owner_disjoint p hf 1536 34816
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
        (p.square (ownerIndex p 256)) (p.square (ownerIndex p 2)) incoming neighbors
        (owner_disjoint p hf 256 2
          (by decide +kernel) (by decide +kernel) (by decide))
    step11 := by
      intro p hf incoming neighbors
      exact Step11.step_sound checked.step11
        (p.square (ownerIndex p 256)) (p.square (ownerIndex p 1536)) incoming neighbors
        (owner_disjoint p hf 256 1536
          (by decide +kernel) (by decide +kernel) (by decide))
    step12 := by
      intro p hf incoming neighbors
      exact Step12.step_sound checked.step12
        (p.square (ownerIndex p 256)) (p.square (ownerIndex p 4096)) incoming neighbors
        (owner_disjoint p hf 256 4096
          (by decide +kernel) (by decide +kernel) (by decide))
    step13 := by
      intro p hf incoming neighbors
      exact Step13.step_sound checked.step13
        (p.square (ownerIndex p 1536)) (p.square (ownerIndex p 256)) incoming neighbors
        (owner_disjoint p hf 1536 256
          (by decide +kernel) (by decide +kernel) (by decide))
    step14 := remaining.step14
    step15 := by
      intro p hf incoming neighbors
      exact Step15.step_sound checked.step15
        (p.square (ownerIndex p 8192)) (p.square (ownerIndex p 12)) incoming neighbors
        (owner_disjoint p hf 8192 12
          (by decide +kernel) (by decide +kernel) (by decide))
    step16 := by
      intro p hf incoming neighbors
      exact Step16.step_sound checked.step16
        (p.square (ownerIndex p 8192)) (p.square (ownerIndex p 256)) incoming neighbors
        (owner_disjoint p hf 8192 256
          (by decide +kernel) (by decide +kernel) (by decide))
    step17 := by
      intro p hf incoming neighbors
      exact Step17.step_sound checked.step17
        (p.square (ownerIndex p 34816)) (p.square (ownerIndex p 1536)) incoming neighbors
        (owner_disjoint p hf 34816 1536
          (by decide +kernel) (by decide +kernel) (by decide))
    step18 := by
      intro p hf incoming neighbors
      exact Step18.step_sound checked.step18
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 2)) incoming neighbors
        (owner_disjoint p hf 1 2
          (by decide +kernel) (by decide +kernel) (by decide))
    step19 := by
      intro p hf incoming neighbors
      exact Step19.step_sound checked.step19
        (p.square (ownerIndex p 1)) (p.square (ownerIndex p 8192)) incoming neighbors
        (owner_disjoint p hf 1 8192
          (by decide +kernel) (by decide +kernel) (by decide))
    step20 := remaining.step20
    step21 := by
      intro p hf incoming neighbors
      exact Step21.step_sound checked.step21
        (p.square (ownerIndex p 2)) (p.square (ownerIndex p 256)) incoming neighbors
        (owner_disjoint p hf 2 256
          (by decide +kernel) (by decide +kernel) (by decide))
    step22 := by
      intro p hf incoming neighbors
      exact Step22.step_sound checked.step22
        (p.square (ownerIndex p 32)) (p.square (ownerIndex p 1536)) incoming neighbors
        (owner_disjoint p hf 32 1536
          (by decide +kernel) (by decide +kernel) (by decide))
    step23 := remaining.step23
    step24 := by
      intro p hf incoming neighbors
      exact Step24.step_sound checked.step24
        (p.square (ownerIndex p 4096)) (p.square (ownerIndex p 2)) incoming neighbors
        (owner_disjoint p hf 4096 2
          (by decide +kernel) (by decide +kernel) (by decide))
    step25 := by
      intro p hf incoming neighbors
      exact Step25.step_sound checked.step25
        (p.square (ownerIndex p 34816)) (p.square (ownerIndex p 192)) incoming neighbors
        (owner_disjoint p hf 34816 192
          (by decide +kernel) (by decide +kernel) (by decide))
    step26 := by
      intro p hf incoming neighbors
      exact Step26.step_sound checked.step26
        (p.square (ownerIndex p 34816)) (p.square (ownerIndex p 1536)) incoming neighbors
        (owner_disjoint p hf 34816 1536
          (by decide +kernel) (by decide +kernel) (by decide))
    step27 := by
      intro p hf incoming neighbors
      exact Step27.step_sound checked.step27
        (p.square (ownerIndex p 34816)) (p.square (ownerIndex p 4096)) incoming neighbors
        (owner_disjoint p hf 34816 4096
          (by decide +kernel) (by decide +kernel) (by decide))
    step28 := remaining.step28
    step29 := by
      intro p hf incoming neighbors
      exact Step29.step_sound checked.step29
        (p.square (ownerIndex p 16)) (p.square (ownerIndex p 1536)) incoming neighbors
        (owner_disjoint p hf 16 1536
          (by decide +kernel) (by decide +kernel) (by decide))
    step30 := by
      intro p hf incoming neighbors
      exact Step30.step_sound checked.step30
        (p.square (ownerIndex p 16)) (p.square (ownerIndex p 34816)) incoming neighbors
        (owner_disjoint p hf 16 34816
          (by decide +kernel) (by decide +kernel) (by decide))
  }

/-- Conditional original-case conclusion. No remaining overlap, entrance,
or chord field is declared true by this adapter. -/
theorem excludes_case_of_remaining (checked : BlockOverlaps) (remaining : Remaining) :
    ExcludesCase 701 :=
  N12Compact.Preservation.C701.excludes_case (pending_of_block_overlaps checked remaining)

#print axioms excludes_case_of_remaining

end
end N12Compact.C701DirectPruning
