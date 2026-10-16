import Compact.Bridge.IndexedChord
import S12.CoreExclusion

/-! Bind a four-square chord transfer to the original normalized packing.
The four distinct owner masks are members of the original coded family. -/

namespace N12Compact.ChordPacking
open S12 S12Pilot

theorem transfer (family : Finset Nat) (masks : Fin 4 → Nat)
    (members : ∀ i, masks i ∈ family) (distinct : Function.Injective masks)
    (source target : List PoseLeaf) (neighbors : Fin 3 → List PoseLeaf)
    (step : ∀ q : Fin 4 → OpenSquare,
      (∀ i, 1 < (q i).side) → (∀ i, InsideContainer (q i)) →
      (∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y)) →
      OrientedPoseCovered source (q 0) →
      (∀ i : Fin 3, OrientedPoseCovered (neighbors i) (q i.succ)) →
      OrientedPoseCovered target (q 0))
    (p : NormalizedPacking) (family_exact : codedMarkerFamily p = family)
    (incoming : OrientedPoseCovered source (p.square (ownerIndex p (masks 0))))
    (neighbor_cover : ∀ i : Fin 3,
      OrientedPoseCovered (neighbors i) (p.square (ownerIndex p (masks i.succ)))) :
    OrientedPoseCovered target (p.square (ownerIndex p (masks 0))) := by
  let q : Fin 4 → OpenSquare := fun i => p.square (ownerIndex p (masks i))
  have side : ∀ i, 1 < (q i).side := by
    intro i
    dsimp [q]
    rw [p.congruent]
    exact p.side_gt_one
  have box : ∀ i, InsideContainer (q i) := fun i => p.contained _
  have disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y) := by
    intro i j different x y overlap
    have mi := ownerIndex_spec p (masks i) (by rw [family_exact]; exact members i)
    have mj := ownerIndex_spec p (masks j) (by rw [family_exact]; exact members j)
    apply p.disjoint (ownerIndex p (masks i)) (ownerIndex p (masks j)) _ x y overlap
    intro same
    exact different (distinct (mi.symm.trans ((congrArg (markerCode p) same).trans mj)))
  exact step q side box disjoint incoming neighbor_cover

#print axioms transfer
end N12Compact.ChordPacking
