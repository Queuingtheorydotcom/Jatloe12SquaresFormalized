import Compact.Geometry.CentralWallEscape
import Compact.Geometry.C977CornerCubic

/-! A steep center-escaping elbow intersects the actual top segment
from (1.6,3) to (2.26,3). Exact auxiliary absence suffices for the outer
point exclusions; no square is assumed to own an unowned auxiliary. -/
namespace N12Compact.SteepElbowTopSegment
open S12 S12Pilot FourSquareAnchors C977CornerCubic
set_option Elab.async false

/-- In the upper half-angle range the endpoint itself lies strictly in
the elbow. The missing right point selects its lower V face. -/
theorem endpoint (A : OpenSquare) (ha : 1<A.side)
    (hc : 0<A.c) (hs : 0≤A.s) (order : A.c≤A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingCenter : ¬A.Inside 2 2) (missingRight : ¬A.Inside 3 (12/5))
    (width : (13/50)*A.c+A.s≤1) : A.Inside (113/50) 3 := by
  have normal : Normal A.s A.c :=
    ⟨hc.le,order,by nlinarith only [A.unit_normal]⟩
  have bounds := normal_bounds normal
  have centerUhi : 2*A.c+2*A.s<A.loU+A.side := by
    nlinarith only [m.2.1,hc,hs]
  have centerVlo : A.loV< -2*A.s+2*A.c := by
    nlinarith only [q.2.2.1,hs]
  have centerVhi : -2*A.s+2*A.c<A.loV+A.side := by
    nlinarith only [p.2.2.2,hc]
  have lowerU : 2*(A.c+A.s)≤A.loU := by
    apply le_of_not_gt
    intro failure
    apply missingCenter
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [failure,centerUhi,centerVlo,centerVhi]
  have rightWidth : A.c+(2/5)*A.s≤1 := by
    linarith only [order,bounds.2.2.2.2.2]
  have rightV : -(3:ℝ)*A.s+(12/5)*A.c≤A.loV := by
    apply le_of_not_gt
    intro lower
    apply missingRight
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [m.1,hc,hs]
    · nlinarith only [lowerU,rightWidth,ha]
    · nlinarith only [lower]
    · nlinarith only [p.2.2.2,order,hc]
  have short : (3/5)*A.c+(37/50)*A.s≤1 := by
    have squared := sq_nonneg ((37/50)*A.c-(3/5)*A.s)
    nlinarith only [A.unit_normal,squared,
      sq_nonneg ((3/5)*A.c+(37/50)*A.s-1)]
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [p.1,hc,hs]
  · nlinarith only [lowerU,width,ha]
  · nlinarith only [q.2.2.1,hc]
  · nlinarith only [rightV,short,ha]

/-- Every positive steep orientation meets the actual top segment.
The two branches use a fixed endpoint or the exact half-angle crossing,
not an angle mesh or a saved enclosure. -/
theorem impossible (A T : OpenSquare) (ha : 1<A.side)
    (hc : 0<A.c) (hs : 0≤A.s) (order : A.c≤A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingCenter : ¬A.Inside 2 2) (missingRight : ¬A.Inside 3 (12/5))
    (missingStrong : ¬A.Inside 3 (5/2))
    (left : T.Inside (8/5) 3) (right : T.Inside (113/50) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ T.Inside x y)) : False := by
  have sp : 0<A.s := lt_of_lt_of_le hc order
  have normal : Normal A.s A.c :=
    ⟨hc.le,order,by nlinarith only [A.unit_normal]⟩
  have bounds := normal_bounds normal
  let z := A.c/(1+A.s)
  have denominator : 0<1+A.s := by linarith only [sp]
  have zp : 0≤z := div_nonneg hc.le denominator.le
  have angle : (1+A.s)*z=A.c := by
    dsimp [z]; field_simp [ne_of_gt denominator]
  have unitAngle : A.c*z=1-A.s := by
    dsimp [z]
    field_simp [ne_of_gt denominator]
    nlinarith only [A.unit_normal]
  by_cases large : 13/50≤z
  · have product := mul_nonneg hc.le (sub_nonneg.mpr large)
    have width : (13/50)*A.c+A.s≤1 := by
      nlinarith only [product,unitAngle]
    exact apart (113/50) 3
      ⟨endpoint A ha hc hs order p q m missingCenter missingRight width,right⟩
  · have small : z≤13/50 := (lt_of_not_ge large).le
    have product := mul_nonneg denominator.le (sub_nonneg.mpr small)
    have sector : A.c≤(16/25)*A.s := by
      nlinarith only [product,angle,bounds.1]
    have crossing := CentralWallEscape.crossing_point (pullSwap A) ha
      sp hc.le (by simpa [pullSwap] using sector) z zp angle unitAngle
      ((inside_pullSwap A _ _).mpr q) ((inside_pullSwap A _ _).mpr p)
      ((inside_pullSwap A _ _).mpr m)
      (fun h => missingStrong ((inside_pullSwap A _ _).mp h))
      (fun h => missingCenter ((inside_pullSwap A _ _).mp h))
    have aPoint : A.Inside (2+z) 3 := (inside_pullSwap A _ _).mp crossing
    let k := (20+50*z)/33
    have kp : 0≤k := by dsimp [k]; positivity
    have k1 : k≤1 := by dsimp [k]; linarith only [small]
    have tPoint : T.Inside (2+z) 3 := by
      have point := inside_segment T (8/5) 3 (113/50) 3 k left right kp k1
      convert point using 1 <;> dsimp [k] <;> ring
    exact apart (2+z) 3 ⟨aPoint,tPoint⟩

#print axioms endpoint
#print axioms impossible
end N12Compact.SteepElbowTopSegment
