import Compact.Core.CachedSupportFan
import Compact.Cases.C898.PairFan

/-! A certified local cache retains the exact original pose and input rows.
Only the small cached vertices and references participate in numeric pair
checks; original-model equalities are proved once when a context is built.
-/

set_option Elab.async false

namespace N12Compact.C898Cached

open S12 S12Pilot IntegerSupport PairPruning C898Shared

structure PoseContext where
  pose : Fin poseCount
  block : List (Fin rowCount)
  keyAngle : Fin 64
  context : CachedSupportFan.Context rows
  inputs_exact : context.inputs = block ++ poseRows pose
  reference_exact : context.reference = references (poseAngle pose)

noncomputable def PoseContext.PairCheck (a b : PoseContext) : Prop :=
  CachedSupportFan.PairCheck a.context b.context
    (fanDirectionKey a.keyAngle b.keyAngle) (fun key => (key + 128) % 256)

noncomputable instance (a b : PoseContext) : Decidable (a.PairCheck b) :=
  inferInstanceAs (Decidable (CachedSupportFan.PairCheck _ _ _ _))

/-- Every original source and neighbor input and both actual inner-reference
containments are retained. The angle key is merely a search hint. -/
theorem PoseContext.pair_sound (a b : PoseContext) (checked : a.PairCheck b)
    (q t : OpenSquare) (hq : (poses a.pose).Realizes q)
    (ht : (poses b.pose).Realizes t)
    (haBlock : ∀ i ∈ a.block, (rows i).Holds ![centerX q, centerY q])
    (hbBlock : ∀ i ∈ b.block, (rows i).Holds ![centerX t, centerY t]) :
    ∃ x y, q.Inside x y ∧ t.Inside x y := by
  have aRef : a.context.reference.value = (poses a.pose).angle.val.reference 1 := by
    rw [a.reference_exact]
    exact references_exact _
  have bRef : b.context.reference.value = (poses b.pose).angle.val.reference 1 := by
    rw [b.reference_exact]
    exact references_exact _
  have ha : a.context.reference.Valid := by
    rw [a.reference_exact]; exact references_valid _
  have hb : b.context.reference.Valid := by
    rw [b.reference_exact]; exact references_valid _
  have hac : a.context.reference.value.Check := by
    rw [aRef]
    exact (poses a.pose).angle.val.reference_checked
      (poses a.pose).angle.property 1 (by norm_num)
  have hbc : b.context.reference.value.Check := by
    rw [bRef]
    exact (poses b.pose).angle.val.reference_checked
      (poses b.pose).angle.property 1 (by norm_num)
  have hs : ∀ i ∈ poseRows a.pose, (rows i).Holds ![centerX q, centerY q] :=
    inputs_hold rows denominators positive_denominators (poseRows a.pose) _ hq.1
  have hn : ∀ i ∈ poseRows b.pose, (rows i).Holds ![centerX t, centerY t] :=
    inputs_hold rows denominators positive_denominators (poseRows b.pose) _ ht.1
  have overlap := CachedSupportFan.pair_sound a.context b.context ha hb hac hbc
    (fanDirectionKey a.keyAngle b.keyAngle) (fun key => (key + 128) % 256)
    checked ![centerX q, centerY q] ![centerX t, centerY t]
    (by rw [a.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (haBlock i) (hs i))
    (by rw [b.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (hbBlock i) (hn i))
  obtain ⟨P, hPq, hPt⟩ := overlap
  refine ⟨P.1, P.2, hq.2 P ?_, ht.2 P ?_⟩
  · simpa only [aRef, Matrix.cons_val_zero, Matrix.cons_val_one] using hPq
  · simpa only [bRef, Matrix.cons_val_zero, Matrix.cons_val_one] using hPt

#print axioms PoseContext.pair_sound

end N12Compact.C898Cached
