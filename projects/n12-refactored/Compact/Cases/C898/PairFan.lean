import Compact.Core.SupportFan
import Compact.Cases.C898.PairRecords

/-! Alternative data representation for the unchanged C898 pair obligations.
This module and its pilot are deliberately separate from the active replay. -/

namespace N12Compact.C898Shared

open S12 S12Pilot IntegerSupport PairPruning

/-- Reference angles are keyed in their cyclic quadrant order. The key is
only a lookup hint; `FanRecord.Check` checks the actual original axis. -/
def fanDirectionKey (a b : Fin 64) (i : Fin 8) : Nat :=
  let angle := if i.val < 4 then a.val else b.val
  let quadrant := match i.val % 4 with
    | 0 => 0
    | 1 => 2
    | 2 => 1
    | _ => 3
  quadrant * 64 + angle

structure FanRecord where
  source : Fin poseCount
  neighbor : Fin poseCount
  block : Nat
  sourceFan : Nat
  neighborFan : Nat

noncomputable def FanRecord.witness
    (fans : Nat → Array (SupportFan.Entry rowCount)) (record : FanRecord) :
    Fin 8 → Support rowCount :=
  SupportFan.witness (fans record.sourceFan) (fans record.neighborFan)
    (fanDirectionKey (poseAngle record.source) (poseAngle record.neighbor))
    (fun key => (key + 128) % 256) ⟨0, 0⟩

noncomputable def FanRecord.Check
    (fans : Nat → Array (SupportFan.Entry rowCount)) (record : FanRecord) : Prop :=
  ∀ i : Fin 8, SupportFan.AxisCheck rows
    (blockRows record.block ++ poseRows record.source) (poseRows record.neighbor)
    (references (poseAngle record.source)) (references (poseAngle record.neighbor))
    i (record.witness fans i)

noncomputable instance (fans : Nat → Array (SupportFan.Entry rowCount))
    (record : FanRecord) : Decidable (record.Check fans) :=
  inferInstanceAs (Decidable (∀ i : Fin 8, _))

theorem FanRecord.sound
    (fans : Nat → Array (SupportFan.Entry rowCount)) (record : FanRecord)
    (checked : record.Check fans) (q t : OpenSquare)
    (hq : (poses record.source).Realizes q)
    (ht : (poses record.neighbor).Realizes t)
    (hblock : ∀ i ∈ blockRows record.block, (rows i).Holds ![centerX q, centerY q]) :
    ∃ x y, q.Inside x y ∧ t.Inside x y := by
  exact PairPruning.actual_overlap rows denominators positive_denominators
    (blockRows record.block) (poseRows record.source) (poseRows record.neighbor)
    (poses record.source) (poses record.neighbor)
    (references (poseAngle record.source)) (references (poseAngle record.neighbor))
    (references_valid _) (references_valid _)
    (references_exact _) (references_exact _) rfl rfl (record.witness fans)
    (fun i => (checked i).toCheck) q t hq ht hblock

#print axioms FanRecord.sound

end N12Compact.C898Shared
