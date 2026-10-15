import Compact.Bridge.AngleSection
import Compact.Core.CoordinateBound

/-! The same long-section argument for either coordinate.  `horizontal`
selects a fixed y-coordinate; otherwise the cut has a fixed x-coordinate. -/

set_option Elab.async false

namespace N12Compact.AxisSection
open S12 S12Pilot IntegerSupport AngleSection LongSectionGeometry SectionCapacity

noncomputable def center (horizontal : Bool) (q : OpenSquare) : ℝ :=
  if horizontal then centerY q else centerX q

def Section (horizontal : Bool) (q : OpenSquare) (cut : ℝ) : Prop :=
  if horizontal then
    ∃ l u : ℝ, 1 < u-l ∧ ∀ x, l < x → x < u → q.Inside x cut
  else VerticalSection q cut

theorem oriented_section (horizontal : Bool) (leaf : PoseLeaf) (w : Radius)
    (checked : w.Check leaf.angle.val) (q : OpenSquare) (ha : 1 < q.side)
    (hq : leaf.AngleWitness q) (cut : ℝ)
    (distance : |cut - center horizontal q| ≤ (w.radius : ℝ)) :
    Section horizontal q cut := by
  cases horizontal with
  | false => exact oriented_vertical leaf w checked q ha hq cut distance
  | true =>
      obtain ⟨r,t,hc,hs,ht0,ht1,hside,hX,hY,hin⟩ := hq
      have hlo : (0 : ℝ) ≤ leaf.angle.val.lower := by exact_mod_cast leaf.angle.property.1
      have hhi : (leaf.angle.val.upper : ℝ) ≤ 1 := by exact_mod_cast leaf.angle.property.2.1
      obtain ⟨hc0,hs0⟩ := normal_nonnegative t (le_trans hlo ht0) (le_trans ht1 hhi)
      have radius := w.bound leaf.angle checked t ht0 ht1
      have near : |cut - centerY r| ≤ sectionRadius r := by
        rw [hY,sectionRadius,hc,hs,abs_of_nonneg hc0,abs_of_nonneg hs0,
          abs_mul,abs_of_nonneg hc0,abs_of_nonneg hs0]
        simpa only [mul_assoc] using le_trans distance radius
      obtain ⟨l,u,length,inside⟩ := horizontal_long_section r cut
        (by simpa only [hside] using ha) near
      exact ⟨l,u,length,fun x hx0 hx1 => (hin x cut).mp (inside x hx0 hx1)⟩

theorem four_impossible (horizontal : Bool) (q : Fin 4 → OpenSquare) (cut : ℝ)
    (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (sections : ∀ i, Section horizontal (q i) cut) : False := by
  cases horizontal with
  | false => exact four_vertical_impossible q cut box disjoint sections
  | true => exact four_on_one_cut q cut box disjoint sections

theorem window_excludes (horizontal : Bool) (lo hi : ℝ) (ordered : lo ≤ hi)
    (q : Fin 4 → OpenSquare) (source : PoseLeaf) (radius : Radius)
    (checked : radius.Check source.angle.val)
    (ha : ∀ i, 1 < (q i).side) (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : source.OrientedRealizes (q 0))
    (neighbors : ∀ cut, lo ≤ cut → cut ≤ hi →
      ∀ i : Fin 3, Section horizontal (q i.succ) cut) :
    ¬ (lo-radius.radius ≤ center horizontal (q 0) ∧
        center horizontal (q 0) ≤ hi+radius.radius) := by
  rintro ⟨low,high⟩
  obtain ⟨cut,hlo,hhi,near⟩ := interval_nearby lo hi (center horizontal (q 0)) radius.radius
    (by exact_mod_cast checked.1) ordered low high
  have first := oriented_section horizontal source radius checked (q 0) (ha 0) incoming.2 cut near
  apply four_impossible horizontal q cut box disjoint
  intro i
  fin_cases i
  · exact first
  · exact neighbors cut hlo hhi 0
  · exact neighbors cut hlo hhi 1
  · exact neighbors cut hlo hhi 2

def orient (horizontal : Bool) (row : Row) : Row :=
  if horizontal then ⟨row.y,row.x,row.constant,row.strict⟩ else row

def lower (horizontal : Bool) (bound : ℚ) (strict : Bool) : Row :=
  orient horizontal (CoordinateBound.lower bound strict)

def upper (horizontal : Bool) (bound : ℚ) (strict : Bool) : Row :=
  orient horizontal (CoordinateBound.upper bound strict)

theorem orient_holds (horizontal : Bool) (row : Row) (x y : ℝ) :
    (orient horizontal row).Holds ![x,y] ↔
      row.Holds (if horizontal then ![y,x] else ![x,y]) := by
  cases horizontal <;> simp [orient,Row.Holds,Row.eval,add_comm,add_left_comm]

theorem holds_lower (horizontal : Bool) (bound : ℚ) (strict : Bool) (q : OpenSquare) :
    (lower horizontal bound strict).Holds ![centerX q,centerY q] ↔
      if strict then (bound : ℝ) < center horizontal q else (bound : ℝ) ≤ center horizontal q := by
  rw [lower,orient_holds,CoordinateBound.holds_lower]
  cases horizontal <;> rfl

theorem holds_upper (horizontal : Bool) (bound : ℚ) (strict : Bool) (q : OpenSquare) :
    (upper horizontal bound strict).Holds ![centerX q,centerY q] ↔
      if strict then center horizontal q < (bound : ℝ) else center horizontal q ≤ (bound : ℝ) := by
  rw [upper,orient_holds,CoordinateBound.holds_upper]
  cases horizontal <;> rfl

#print axioms window_excludes
end N12Compact.AxisSection
