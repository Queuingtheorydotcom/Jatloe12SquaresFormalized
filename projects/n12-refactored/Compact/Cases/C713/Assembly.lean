import Compact.Cases.C713.RecipeInitial.Entry
import Compact.Cases.C713.ChordDirect

/-! The exact C713 whole chain with its remaining numerical stages explicit.
The initial covers and occupied-row height transfer are actual original-model
lemmas. The nine fields below are the unchanged pair-stage obligations that
must still be supplied by checked numerical adapters. This module does not
construct an unconditional case exclusion or declare any missing field true.
-/

namespace N12Compact.C713Assembly
open S12 S12Pilot C713Shared
set_option Elab.async false

/-- The actual full source and neighbor covers, including every angle/pose. -/
def PairTransition (source neighbor target : List PoseLeaf) : Prop :=
  ∀ q t : OpenSquare,
    OrientedPoseCovered source q → OrientedPoseCovered neighbor t →
    (∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) → OrientedPoseCovered target q

/-- Exact outstanding pair obligations; the former chord step5 is absent
because its actual occupied-row replacement is already part of the assembly. -/
structure PairStages : Prop where
  step0 : PairTransition
    continuousScout713Domain0_0 continuousScout713Domain9_0 continuousScout713Domain0_1
  step1 : PairTransition
    continuousScout713Domain1_0 continuousScout713Domain0_1 continuousScout713Domain1_2
  step2 : PairTransition
    continuousScout713Domain1_2 continuousScout713Domain8_0 continuousScout713Domain1_3
  step3 : PairTransition
    continuousScout713Domain5_0 continuousScout713Domain11_0 continuousScout713Domain5_4
  step4 : PairTransition
    continuousScout713Domain6_0 continuousScout713Domain10_0 continuousScout713Domain6_5
  step6 : PairTransition
    continuousScout713Domain7_6 continuousScout713Domain1_3 continuousScout713Domain7_7
  step7 : PairTransition
    continuousScout713Domain7_7 continuousScout713Domain6_5 continuousScout713Domain7_8
  step8 : PairTransition
    continuousScout713Domain8_0 continuousScout713Domain5_4 continuousScout713Domain8_9
  step9 : PairTransition
    continuousScout713Domain8_9 continuousScout713Domain7_8 continuousScout713Domain8_10

private theorem owner_disjoint (p : NormalizedPacking)
    (family : codedMarkerFamily p = case713Family) (a b : Nat)
    (ha : a ∈ case713Family) (hb : b ∈ case713Family) (distinct : a ≠ b) :
    ∀ x y, ¬((p.square (ownerIndex p a)).Inside x y ∧
      (p.square (ownerIndex p b)).Inside x y) := by
  apply p.disjoint
  intro equal
  apply distinct
  have left := ownerIndex_spec p a (by rw [family]; exact ha)
  have right := ownerIndex_spec p b (by rw [family]; exact hb)
  exact left.symm.trans ((congrArg (markerCode p) equal).trans right)

/-- Supplying the nine genuine pair stages finishes the whole original C713
family. All size, container, ownership and disjointness facts come from p;
no geometric or certificate premise is silently added to an ExcludesCase. -/
theorem family_impossible_of_pair_stages (stages : PairStages)
    (p : NormalizedPacking) (family : codedMarkerFamily p = case713Family) : False := by
  have h0 := C713Entry.owner0_cover p family
  have h1 := C713Entry.owner1_cover p family
  have h5 := C713Entry.owner5_cover p family
  have h6 := C713Entry.owner6_cover p family
  have h7 := C713Entry.owner7_cover p family
  have h8 := C713Entry.owner8_cover p family
  have h9 := C713Entry.owner9_cover p family
  have h10 := C713Entry.owner10_cover p family
  have h11 := C713Entry.owner11_cover p family
  have after0 := stages.step0
    (p.square (ownerIndex p 1)) (p.square (ownerIndex p 8192)) h0 h9
    (owner_disjoint p family 1 8192 (by decide +kernel) (by decide +kernel) (by decide))
  have after1 := stages.step1
    (p.square (ownerIndex p 2)) (p.square (ownerIndex p 1)) h1 after0
    (owner_disjoint p family 2 1 (by decide +kernel) (by decide +kernel) (by decide))
  have after2 := stages.step2
    (p.square (ownerIndex p 2)) (p.square (ownerIndex p 4096)) after1 h8
    (owner_disjoint p family 2 4096 (by decide +kernel) (by decide +kernel) (by decide))
  have after3 := stages.step3
    (p.square (ownerIndex p 192)) (p.square (ownerIndex p 32768)) h5 h11
    (owner_disjoint p family 192 32768 (by decide +kernel) (by decide +kernel) (by decide))
  have after4 := stages.step4
    (p.square (ownerIndex p 512)) (p.square (ownerIndex p 16384)) h6 h10
    (owner_disjoint p family 512 16384 (by decide +kernel) (by decide +kernel) (by decide))
  have after5 := C713ChordDirect.source_to_after_height p family h7
  have after6 := stages.step6
    (p.square (ownerIndex p 2304)) (p.square (ownerIndex p 2)) after5 after2
    (owner_disjoint p family 2304 2 (by decide +kernel) (by decide +kernel) (by decide))
  have after7 := stages.step7
    (p.square (ownerIndex p 2304)) (p.square (ownerIndex p 512)) after6 after4
    (owner_disjoint p family 2304 512 (by decide +kernel) (by decide +kernel) (by decide))
  have after8 := stages.step8
    (p.square (ownerIndex p 4096)) (p.square (ownerIndex p 192)) h8 after3
    (owner_disjoint p family 4096 192 (by decide +kernel) (by decide +kernel) (by decide))
  have after9 := stages.step9
    (p.square (ownerIndex p 4096)) (p.square (ownerIndex p 2304)) after8 after7
    (owner_disjoint p family 4096 2304 (by decide +kernel) (by decide +kernel) (by decide))
  obtain ⟨leaf,member,_⟩ := after9
  exact List.not_mem_nil member

#print axioms family_impossible_of_pair_stages
end N12Compact.C713Assembly
