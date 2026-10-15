import Compact.Cases.C898.RecipeInitial.Entry
import Compact.Cases.C898.MixedCached
import Completion.Contracts
import Compact.Assembly.RowIdentity

/-! Alternative compact assembly of the original whole case. The public
family and ExcludesCase statements have exactly their original premises;
the extra internal chord facts are proved from that same packing below.
This module and the legacy Complete module are alternative entry points. -/

namespace N12Compact.C898
open S12 S12Pilot S12Completion FourSquareAnchors
set_option Elab.async false
set_option maxRecDepth 10000

theorem family_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p = case898Family) : False := by
  have hc0 := C898Entry.owner0_cover p hf
  have hc1 := C898Entry.owner1_cover p hf
  have hc2 := C898Entry.owner2_cover p hf
  have hc3 := C898Entry.owner3_cover p hf
  have hc5 := C898Entry.owner5_cover p hf
  have hc6 := C898Entry.owner6_cover p hf
  have hc7 := C898Entry.owner7_cover p hf
  have hc8 := C898Entry.owner8_cover p hf
  have hc9 := C898Entry.owner9_cover p hf
  have hc10 := C898Entry.owner10_cover p hf
  have hc11 := C898Entry.owner11_cover p hf
  let masks : Fin 11 → Nat := ![1,2,12,16,768,1056,2048,4096,8192,16384,32768]
  let q : Fin 11 → OpenSquare := fun i => p.square (ownerIndex p (masks i))
  have hm : ∀ i, masks i ∈ case898Family := by decide +kernel
  have hi : Function.Injective masks := by decide +kernel
  have ha : ∀ i, 1 < (q i).side := by
    intro i
    dsimp [q]
    rw [p.congruent]
    exact p.side_gt_one
  have hb : ∀ i, InsideContainer (q i) := fun i => p.contained _
  have hd : ∀ i j, i ≠ j → ∀ x y, ¬((q i).Inside x y ∧ (q j).Inside x y) := by
    intro i j hne x y hp
    have hmi := ownerIndex_spec p (masks i) (by rw [hf]; exact hm i)
    have hmj := ownerIndex_spec p (masks j) (by rw [hf]; exact hm j)
    apply p.disjoint (ownerIndex p (masks i)) (ownerIndex p (masks j)) _ x y hp
    intro he
    exact hne (hi (hmi.symm.trans ((congrArg (markerCode p) he).trans hmj)))
  have cap : (q 4).side ≤ 1001/1000 := by
    dsimp [q]
    rw [p.congruent]
    exact p.side_le
  have owned := (PointPremises.sound case898Domain5 commonPoints898
    C898DirectInitial.inside5 C898DirectInitial.outside5
    C898Entry.owner5_premises_checked p hf).1
  have left_inside : (q 4).Inside (33/20) (33/20) := by
    have h := owned ((33/20 : ℚ), (33/20 : ℚ)) (by decide +kernel)
    norm_num at h
    exact h
  have right_inside : (q 4).Inside (47/20) (33/20) := by
    have h := owned ((47/20 : ℚ), (33/20 : ℚ)) (by decide +kernel)
    norm_num at h
    exact h
  have left : ClosedInside (q 4) (33/20) (33/20) :=
    ⟨left_inside.1.le, left_inside.2.1.le, left_inside.2.2.1.le, left_inside.2.2.2.le⟩
  have right : ClosedInside (q 4) (47/20) (33/20) :=
    ⟨right_inside.1.le, right_inside.2.1.le, right_inside.2.2.1.le, right_inside.2.2.2.le⟩
  exact C898CachedAssembly.mixed_impossible q ha hb hd cap left right
    hc0 hc1 hc2 hc3 hc5 hc6 hc7 hc8 hc9 hc10 hc11

private theorem row_checked :
    (RowIdentity.rowAt 485).originalId = 898 ∧
    (RowIdentity.rowAt 485).groups = case898Family := by decide +kernel

theorem row_family : ∀ r ∈ retainedRows, r.originalId = 898 → r.groups = case898Family :=
  RowIdentity.family_at 485 898 case898Family row_checked

theorem family_retained : ∃ r ∈ retainedRows, r.originalId = 898 ∧ r.groups = case898Family := by
  refine ⟨RowIdentity.rowAt 485, ?_, row_checked⟩
  apply List.mem_filter.mpr
  refine ⟨RowIdentity.rowAt_mem _, ?_⟩
  apply decide_eq_true
  rw [row_checked.1]
  decide +kernel

theorem excludes_case : ExcludesCase 898 := by
  intro r hr hid p hf
  exact family_impossible p (hf.trans (row_family r hr hid))

#print axioms family_impossible
#print axioms excludes_case
end N12Compact.C898
