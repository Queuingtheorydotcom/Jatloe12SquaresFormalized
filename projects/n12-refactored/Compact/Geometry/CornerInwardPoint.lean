import Compact.Geometry.ClosedFrames
import Compact.Geometry.ClosedPointExclusion
import S12.Container

/-! The genuine corner square contains a point displaced inward by its
actual side excess. This uses both container walls and both corner markers;
it is stronger than merely retaining the fixed seed point (1,1). -/
namespace N12Compact.CornerInwardPoint

open S12 S12Pilot FourSquareAnchors

private theorem transverse_upper (a c s u v : ℝ)
    (ha : 1 ≤ a) (size : a ≤ 1001/1000)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (wall : 0 ≤ s*u+c*v)
    (pointU : u ≤ (457/500)*c+s)
    (pointV : -(457/500)*s+c ≤ v+a) :
    a*(c-s) ≤ v+a := by
  by_cases slope : c/20 ≤ s
  · have first := mul_nonneg
      (show 0 ≤ a-457/500 by linarith only [ha]) (sub_nonneg.mpr slope)
    have second := mul_nonneg hc
      (show 0 ≤ (a-457/500)/20-(a-1) by linarith only [size])
    nlinarith only [pointV,first,second]
  · have small : s ≤ c/20 := (lt_of_not_ge slope).le
    have cPos : 0 < c := by
      by_contra failure
      have zero : c=0 := le_antisymm (le_of_not_gt failure) hc
      have zero' : s=0 := by linarith only [small,hs,zero]
      rw [zero,zero'] at unit
      norm_num at unit
    have cHigh : c ≤ 1 := by
      nlinarith only [unit,sq_nonneg s,sq_nonneg (c-1)]
    have first := mul_nonneg (mul_nonneg (show 0 ≤ a by linarith only [ha]) hc)
      (sub_nonneg.mpr cHigh)
    have ac := mul_nonneg hc (show 0 ≤ a-1 by linarith only [ha])
    have second := mul_nonneg hs
      (show 0 ≤ (a-457/500)*c-s by nlinarith only [ac,small,hc])
    have third := mul_nonneg hs (sub_nonneg.mpr pointU)
    by_contra failure
    have positive := mul_pos cPos (sub_pos.mpr (lt_of_not_ge failure))
    nlinarith only [first,second,third,wall,positive]

private theorem in_frame (q : OpenSquare)
    (hc : 0 ≤ q.c) (hs : 0 ≤ q.s)
    (ha : 1 ≤ q.side) (size : q.side ≤ 1001/1000)
    (wall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (P : ClosedInside q 1 (457/500))
    (Q : ClosedInside q (457/500) 1) :
    ClosedInside q q.side q.side := by
  obtain ⟨wallX,wallY⟩ := positive_frame_wall_bounds q hc hs wall
  have wx : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side) := by
    dsimp [centerX] at wallX
    nlinarith only [wallX]
  have wy : 0 ≤ q.s*q.loU+q.c*q.loV := by
    dsimp [centerY] at wallY
    nlinarith only [wallY]
  have cHigh : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have sHigh : q.s ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.c,sq_nonneg (q.s-1)]
  have uWall : q.side*q.c*q.s ≤ q.loU := by
    have first := mul_nonneg hc wx
    have second := mul_nonneg hs wy
    have identity := congrArg (fun z : ℝ => q.loU*z) q.unit_normal
    dsimp only at identity
    nlinarith only [first,second,identity]
  have uUpper : q.c*q.side+q.s*q.side ≤ q.loU+q.side := by
    have factor := mul_nonneg (sub_nonneg.mpr cHigh) (sub_nonneg.mpr sHigh)
    have product := mul_nonneg (show 0 ≤ q.side by linarith only [ha]) factor
    nlinarith only [uWall,product]
  have uLower : q.loU ≤ q.c*q.side+q.s*q.side := by
    have first := mul_nonneg hc (show 0 ≤ q.side-1 by linarith only [ha])
    have second := mul_nonneg hs (show 0 ≤ q.side-457/500 by linarith only [ha])
    nlinarith only [P.1,first,second]
  have vUpper := transverse_upper q.side q.c q.s q.loU q.loV
    ha size hc hs q.unit_normal wy
    (by linarith only [Q.1]) (by linarith only [Q.2.2.2])
  have vLower := transverse_upper q.side q.s q.c q.loU (-q.loV-q.side)
    ha size hs hc (by nlinarith only [q.unit_normal])
    (by nlinarith only [wx])
    (by linarith only [P.1]) (by linarith only [P.2.2.1])
  exact ⟨uLower,uUpper,by nlinarith only [vLower],by nlinarith only [vUpper]⟩

/-- The point at distance exactly `q.side` from both walls belongs to the
closed square. No orientation or center-location assumption is needed. -/
theorem first_quadrant (q : OpenSquare)
    (ha : 1 ≤ q.side) (size : q.side ≤ 1001/1000)
    (wall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (P : ClosedInside q 1 (457/500))
    (Q : ClosedInside q (457/500) 1) :
    ClosedInside q q.side q.side := by
  obtain ⟨r,hc,hs,side,inside,closed⟩ := ClosedFrames.positive_frame q
  have hw : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y :=
    fun x y h => wall x y ((inside x y).mp h)
  have result := in_frame r hc.le hs (by simpa only [side] using ha)
    (by simpa only [side] using size) hw ((closed _ _).mpr P) ((closed _ _).mpr Q)
  exact (closed _ _).mp (by simpa only [side] using result)

private theorem closed_pullY (q : OpenSquare) (x y : ℝ) :
    ClosedInside (pullY q) x y ↔ ClosedInside q x (4-y) := by
  dsimp [ClosedInside,pullY]
  constructor <;> rintro ⟨h₀,h₁,h₂,h₃⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

/-- Actual upper-left corner owner, including its two original strict
markers and true containment. Closed membership suffices for exclusion by
the open interior of any disjoint square. -/
theorem upper_left (E : OpenSquare)
    (ha : 1 < E.side) (size : E.side ≤ 1001/1000)
    (box : InsideContainer E)
    (P : E.Inside 1 (1543/500)) (Q : E.Inside (457/500) 3) :
    ClosedInside E E.side (4-E.side) := by
  have P' : (pullY E).Inside 1 (457/500) := by
    apply (inside_pullY E _ _).mpr
    convert P using 1 <;> norm_num
  have Q' : (pullY E).Inside (457/500) 1 := by
    apply (inside_pullY E _ _).mpr
    convert Q using 1 <;> norm_num
  have container := container_pullY E box
  have result := first_quadrant (pullY E) ha.le size
    (fun x y h => ⟨(container x y h).1,(container x y h).2.2.1⟩)
    ⟨P'.1.le,P'.2.1.le,P'.2.2.1.le,P'.2.2.2.le⟩
    ⟨Q'.1.le,Q'.2.1.le,Q'.2.2.1.le,Q'.2.2.2.le⟩
  exact (closed_pullY E E.side E.side).mp result

/-- The side-dependent corner point is genuinely excluded from any
disjoint square, even if it lies on E's boundary. -/
theorem outside_upper_left (B E : OpenSquare)
    (ha : 1 < E.side) (size : E.side ≤ 1001/1000)
    (box : InsideContainer E)
    (P : E.Inside 1 (1543/500)) (Q : E.Inside (457/500) 3)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ E.Inside x y)) :
    ¬ B.Inside E.side (4-E.side) :=
  ClosedPointExclusion.outside_of_closed B E _ _ apart
    (upper_left E ha size box P Q)

#print axioms upper_left

end N12Compact.CornerInwardPoint
