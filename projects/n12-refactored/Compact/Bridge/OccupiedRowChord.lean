import Compact.Geometry.CentralBarHeight
import Compact.Bridge.AngleSection

/-! A blocked row forces an entire oriented chord cut from original point
ownership.  The angle witness is used with its actual equivalent square;
no equality of frame-dependent radius expressions is assumed. -/

namespace N12Compact.OccupiedRowChord
open S12 S12Pilot FourSquareAnchors AngleSection LongSectionGeometry

theorem above_radius (leaf : PoseLeaf) (radius : Radius)
    (checked : radius.Check leaf.angle.val) (q : OpenSquare)
    (ha : 1 < q.side) (cap : q.side ≤ 1001/1000)
    (box : InsideContainer q) (angle : leaf.AngleWitness q)
    (neighbors : Fin 3 → OpenSquare) (h x y : ℝ)
    (top : q.Inside x y) (gap : h+51/100 ≤ y)
    (points : ∀ i, ClosedInside (neighbors i) ((i.val : ℝ)+1) h)
    (apart : ∀ i x y, ¬ (q.Inside x y ∧ (neighbors i).Inside x y)) :
    h + (radius.radius : ℝ) < centerY q := by
  obtain ⟨r,t,hc,hs,ht0,ht1,hside,hX,hY,hin⟩ := angle
  have ha' : 1 < r.side := by simpa only [hside] using ha
  have cap' : r.side ≤ 1001/1000 := by simpa only [hside] using cap
  have box' : InsideContainer r := fun x y hp => box x y ((hin x y).mp hp)
  have top' : r.Inside x y := (hin x y).mpr top
  have closed : ClosedInside r x y :=
    ⟨top'.1.le,top'.2.1.le,top'.2.2.1.le,top'.2.2.2.le⟩
  have apart' : ∀ i x y, ¬ (r.Inside x y ∧ (neighbors i).Inside x y) := by
    intro i x y hp
    exact apart i x y ⟨(hin x y).mp hp.1,hp.2⟩
  have above := CentralBarHeight.from_three_occupied_points r neighbors h x y
    ha' cap' box' closed gap points apart'
  have htlo : (0 : ℝ) ≤ leaf.angle.val.lower := by
    exact_mod_cast leaf.angle.property.1
  have hthi : (leaf.angle.val.upper : ℝ) ≤ 1 := by
    exact_mod_cast leaf.angle.property.2.1
  obtain ⟨hc0,hs0⟩ := normal_nonnegative t (htlo.trans ht0) (ht1.trans hthi)
  have bound := radius.bound leaf.angle checked t ht0 ht1
  have radius_le : (radius.radius : ℝ) ≤ sectionRadius r := by
    simpa only [sectionRadius,hc,hs,abs_of_nonneg hc0,abs_of_nonneg hs0,
      abs_mul,mul_assoc] using bound
  rw [hY] at above
  linarith only [above,radius_le]

/-- Any historical chord whose upper endpoint is at or below the occupied
row has only its above-window branch.  C713 uses hi=1.67873435 and h=1.74. -/
theorem above_window (leaf : PoseLeaf) (radius : Radius)
    (checked : radius.Check leaf.angle.val) (q : OpenSquare)
    (ha : 1 < q.side) (cap : q.side ≤ 1001/1000)
    (box : InsideContainer q) (angle : leaf.AngleWitness q)
    (neighbors : Fin 3 → OpenSquare) (h x y upper : ℝ)
    (upper_le : upper ≤ h) (top : q.Inside x y) (gap : h+51/100 ≤ y)
    (points : ∀ i, ClosedInside (neighbors i) ((i.val : ℝ)+1) h)
    (apart : ∀ i x y, ¬ (q.Inside x y ∧ (neighbors i).Inside x y)) :
    upper + (radius.radius : ℝ) < centerY q := by
  have bound := above_radius leaf radius checked q ha cap box angle
    neighbors h x y top gap points apart
  linarith only [bound,upper_le]

#print axioms above_window
end N12Compact.OccupiedRowChord
