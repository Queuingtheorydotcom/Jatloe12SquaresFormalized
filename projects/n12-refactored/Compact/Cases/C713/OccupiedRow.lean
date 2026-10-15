import Compact.Cases.C713.EntryPoints
import Compact.Bridge.OccupiedRowChord

/-! Bind the blocked-row argument to the actual original C713 packing.
The four point declarations are authenticated CommonPoints713 entries7,
22,36 and27. No propagated geometric cover or forced auxiliary assignment
is a premise of this bridge. EntryPoints must be independently replayed. -/

namespace N12Compact.C713OccupiedRow
open S12 S12Pilot FourSquareAnchors AngleSection

private theorem close {q : OpenSquare} {x y : ℝ} (h : q.Inside x y) :
    ClosedInside q x y := ⟨h.1.le,h.2.1.le,h.2.2.1.le,h.2.2.2.le⟩

theorem above_radius (p : NormalizedPacking)
    (family : codedMarkerFamily p = case713Family)
    (leaf : PoseLeaf) (radius : Radius) (checked : radius.Check leaf.angle.val)
    (angle : leaf.AngleWitness (p.square (ownerIndex p 2304))) :
    (87/50 : ℝ) + (radius.radius : ℝ) < centerY (p.square (ownerIndex p 2304)) := by
  let masks : Fin 3 → Nat := ![2,512,16384]
  let neighbors : Fin 3 → OpenSquare := fun i => p.square (ownerIndex p (masks i))
  have member : ∀ i, masks i ∈ case713Family := by decide +kernel
  have distinct : ∀ i, 2304 ≠ masks i := by decide +kernel
  have sourceCode : markerCode p (ownerIndex p 2304) = 2304 :=
    ownerIndex_spec p 2304 (by rw [family]; decide +kernel)
  have apart : ∀ i x y, ¬ ((p.square (ownerIndex p 2304)).Inside x y ∧
      (neighbors i).Inside x y) := by
    intro i x y hp
    have otherCode := ownerIndex_spec p (masks i) (by rw [family]; exact member i)
    apply p.disjoint (ownerIndex p 2304) (ownerIndex p (masks i)) _ x y hp
    intro same
    exact distinct i (sourceCode.symm.trans
      ((congrArg (markerCode p) same).trans otherCode))
  have left : (p.square (ownerIndex p 2)).Inside 1 (87/50) := by
    have h := commonPoint713_7.sound p family
    change (p.square (ownerIndex p 2)).Inside ((1 : ℚ) : ℝ) ((87/50 : ℚ) : ℝ) at h
    norm_num at h
    exact h
  have middle : (p.square (ownerIndex p 512)).Inside 2 (87/50) := by
    have h := commonPoint713_22.sound p family
    change (p.square (ownerIndex p 512)).Inside (2 : ℝ) ((87/50 : ℚ) : ℝ) at h
    norm_num at h
    exact h
  have right : (p.square (ownerIndex p 16384)).Inside 3 (87/50) := by
    have h := commonPoint713_36.sound p family
    change (p.square (ownerIndex p 16384)).Inside (3 : ℝ) ((87/50 : ℚ) : ℝ) at h
    norm_num at h
    exact h
  have top : (p.square (ownerIndex p 2304)).Inside (33/20) (47/20) := by
    have h := commonPoint713_27.sound p family
    change (p.square (ownerIndex p 2304)).Inside
      ((33/20 : ℚ) : ℝ) ((47/20 : ℚ) : ℝ) at h
    norm_num at h
    exact h
  have points : ∀ i, ClosedInside (neighbors i) ((i.val : ℝ)+1) (87/50) := by
    intro i
    fin_cases i
    · simpa [neighbors,masks] using close left
    · norm_num [neighbors,masks]
      exact close middle
    · norm_num [neighbors,masks]
      exact close right
  exact OccupiedRowChord.above_radius leaf radius checked _
    (by rw [p.congruent]; exact p.side_gt_one)
    (by rw [p.congruent]; exact p.side_le)
    (p.contained _) angle neighbors (87/50) (33/20) (47/20)
    top (by norm_num) points apart

/-- The original window's above-branch cut follows without any of its
three propagated neighbor-domain premises. -/
theorem above_historical_window (p : NormalizedPacking)
    (family : codedMarkerFamily p = case713Family)
    (leaf : PoseLeaf) (radius : Radius) (checked : radius.Check leaf.angle.val)
    (angle : leaf.AngleWitness (p.square (ownerIndex p 2304))) :
    (33574687/20000000 : ℝ) + (radius.radius : ℝ) <
      centerY (p.square (ownerIndex p 2304)) := by
  have h := above_radius p family leaf radius checked angle
  linarith only [h]

#print axioms above_radius
#print axioms above_historical_window
end N12Compact.C713OccupiedRow
