import Compact.Geometry.CentralWallPairAxes
import Compact.Geometry.CentralWallParallelMargin

/-! The two remaining longitudinal separators contradict the full square
supports and the actual right wall. No virtual wall replaces the neighbor. -/
namespace N12Compact.CentralWallPairSupport
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open CentralWallPairAxes CentralWallLongitudinal
set_option Elab.async false

theorem support_formulas (A R : OpenSquare)
    (dot : 0 ≤ A.c*R.c+A.s*R.s) (cross : 0 ≤ A.c*R.s-A.s*R.c) :
    upper A R.c R.s =
      (A.c*R.c+A.s*R.s)*(A.loU+A.side)+
      (A.c*R.s-A.s*R.c)*(A.loV+A.side) ∧
    lower R A.c A.s =
      (A.c*R.c+A.s*R.s)*R.loU-
      (A.c*R.s-A.s*R.c)*(R.loV+R.side) := by
  have dot' : 0 ≤ R.c*A.c+R.s*A.s := by nlinarith only [dot]
  have cross' : 0 ≤ -R.c*A.s+R.s*A.c := by nlinarith only [cross]
  constructor
  · dsimp [upper,supportRadius,centerX,centerY]
    rw [abs_of_nonneg dot',abs_of_nonneg cross']
    ring
  · dsimp [lower,supportRadius,centerX,centerY]
    rw [abs_of_nonneg dot,abs_of_nonpos (show -A.c*R.s+A.s*R.c ≤ 0 by
      nlinarith only [cross])]
    ring

theorem shallow_wall_of_central_axis (A R : OpenSquare)
    (ha : 1 < A.side) (ac : 0 < A.c) (aNonneg : 0 ≤ A.s)
    (rc : 0 < R.c) (rs : 0 ≤ R.s) (narrow : 12*A.s ≤ 5*A.c)
    (cross : 0 ≤ A.c*R.s-A.s*R.c)
    (lower : 2*A.c+2*A.s ≤ A.loU)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (axis : A.loU+A.side ≤ ABTransverse.lower R A.c A.s) : R.s < R.c := by
  let d := A.c*R.c+A.s*R.s
  let k := A.c*R.s-A.s*R.c
  have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos ac rc) (mul_nonneg aNonneg rs)
  have kn : 0 ≤ k := cross
  have formula := (support_formulas A R dp.le cross).2
  change ABTransverse.lower R A.c A.s=d*R.loU-k*(R.loV+R.side) at formula
  by_contra notShallow
  have steep : R.c ≤ R.s := le_of_not_gt notShallow
  have highU := mul_lt_mul_of_pos_left marker.1 dp
  have highV := mul_le_mul_of_nonneg_left high.2.2.2.le kn
  have compose : d*(R.c*(1543/500)+R.s*2)-
      k*(-R.s*3+R.c*(12/5)) =
      (1543/500)*A.c+2*A.s-k*((2/5)*R.c+(43/500)*R.s) := by
    dsimp [d,k]
    linear_combination ((1543/500)*A.c+2*A.s)*R.unit_normal
  have first := mul_nonneg (sub_nonneg.mpr steep)
    (show 0 ≤ (2/5)*A.c-(43/500)*A.s by linarith only [narrow,ac])
  have second := mul_nonneg rc.le
    (show 0 ≤ (157/500)*A.c-(243/500)*A.s by linarith only [narrow,ac])
  have gain : (43/500)*A.c ≤ k*((2/5)*R.c+(43/500)*R.s) := by
    have weighted := mul_nonneg rc.le (add_nonneg first second)
    have identity : k*((2/5)*R.c+(43/500)*R.s)-(43/500)*A.c =
        R.c*((R.s-R.c)*((2/5)*A.c-(43/500)*A.s)+
          R.c*((157/500)*A.c-(243/500)*A.s)) := by
      dsimp [k]
      linear_combination (43/500)*A.c*R.unit_normal
    nlinarith only [weighted,identity]
  have acu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,ac]
  have strictSupport : ABTransverse.lower R A.c A.s <
      (1543/500)*A.c+2*A.s-k*((2/5)*R.c+(43/500)*R.s) := by
    rw [formula,← compose]
    exact (sub_lt_sub_right highU _).trans_le (sub_le_sub_left highV _)
  have supportCap : (1543/500)*A.c+2*A.s-k*((2/5)*R.c+(43/500)*R.s) ≤
      3*A.c+2*A.s := by
    convert sub_le_sub_left gain ((1543/500)*A.c+2*A.s) using 1 <;> ring
  have needed : 2*A.c+2*A.s+A.side < 3*A.c+2*A.s :=
    ((add_le_add_right lower A.side).trans axis).trans_lt
      (strictSupport.trans_le supportCap)
  linarith only [needed,ha,acu]

theorem central_axis_impossible (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (ac : 0 < A.c) (aNonneg : 0 ≤ A.s) (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (narrow : 12*A.s ≤ 5*A.c) (cross : 0 ≤ A.c*R.s-A.s*R.c)
    (lower : 2*A.c+2*A.s ≤ A.loU)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (axis : A.loU+A.side ≤ ABTransverse.lower R A.c A.s) : False := by
  have shallow := shallow_wall_of_central_axis A R ha ac aNonneg rc rs narrow
    cross lower marker high axis
  let d := A.c*R.c+A.s*R.s
  let k := A.c*R.s-A.s*R.c
  have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos ac rc) (mul_nonneg aNonneg rs)
  have kn : 0 ≤ k := cross
  have formula := (support_formulas A R dp.le cross).2
  change ABTransverse.lower R A.c A.s=d*R.loU-k*(R.loV+R.side) at formula
  have wall := mul_le_mul_of_nonneg_left (CentralWallEscape.right_wall R box) dp.le
  have markerBound := mul_le_mul_of_nonneg_left marker.2.2.1.le aNonneg
  have cancellation : d*R.s-R.c*k=A.s := by
    dsimp [d,k]
    linear_combination A.s*R.unit_normal
  have supportBound : R.c*ABTransverse.lower R A.c A.s ≤
      R.c*(4*A.c+2*A.s)+(457/500)*A.s*R.s-R.side*R.c*(d+k) := by
    have expanded : R.c*ABTransverse.lower R A.c A.s =
        d*(R.c*(R.loU+R.side)-R.s*R.loV)+A.s*R.loV-
          R.side*R.c*(d+k) := by
      rw [formula]
      nlinarith only [congrArg (fun x : ℝ => x*R.loV) cancellation]
    calc
      R.c*ABTransverse.lower R A.c A.s =
          d*(R.c*(R.loU+R.side)-R.s*R.loV)+A.s*R.loV-
            R.side*R.c*(d+k) := expanded
      _ ≤ d*4+A.s*(-R.s*(1543/500)+R.c*2)-R.side*R.c*(d+k) :=
        sub_le_sub_right (add_le_add wall markerBound) _
      _ = _ := by dsimp [d]; ring
  have scaledAxis := mul_le_mul_of_nonneg_left axis rc.le
  have scaledLower := mul_le_mul_of_nonneg_left lower rc.le
  have original := CentralWallParallelMargin.parallel_margin
    (show C977CornerCubic.Normal A.c A.s from
      ⟨aNonneg,by linarith only [narrow,ac],A.unit_normal⟩)
    (show C977CornerCubic.Normal R.c R.s from ⟨rs,shallow.le,R.unit_normal⟩)
    narrow cross
  have ratio : R.c*(R.s/R.c)=R.s := by field_simp [ne_of_gt rc]
  have scaledMargin := mul_nonneg rc.le original
  have strict := mul_pos (sub_pos.mpr ha)
    (mul_pos rc (show 0 < 1+d+k by linarith only [dp,kn]))
  rw [← same] at supportBound
  have scaledMargin' : 0 ≤ R.c*(1+d+k-2*A.c-(457/500)*A.s*(R.s/R.c)) := by
    dsimp [d,k]
    nlinarith only [scaledMargin]
  have ratioScaled := congrArg (fun x : ℝ => (457/500)*A.s*x) ratio
  dsimp at ratioScaled
  have scaleIdentity : R.c*((457/500)*A.s*(R.s/R.c)) =
      (457/500)*A.s*R.s := by
    calc
      _ = (457/500)*A.s*(R.c*(R.s/R.c)) := by ring
      _ = _ := ratioScaled
  rw [mul_sub,scaleIdentity] at scaledMargin'
  have combined : R.c*(2*A.c+2*A.s+A.side) ≤
      R.c*(4*A.c+2*A.s)+(457/500)*A.s*R.s-A.side*R.c*(d+k) := by
    calc
      _ = R.c*(2*A.c+2*A.s)+R.c*A.side := by ring
      _ ≤ R.c*A.loU+R.c*A.side := add_le_add_right scaledLower _
      _ = R.c*(A.loU+A.side) := by ring
      _ ≤ _ := scaledAxis.trans supportBound
  have nonpositive : (A.side-1)*(R.c*(1+d+k)) ≤ 0 := by
    calc
      _ = (R.c*(2*A.c+2*A.s+A.side)-
          (R.c*(4*A.c+2*A.s)+(457/500)*A.s*R.s-A.side*R.c*(d+k)))-
          (R.c*(1+d+k-2*A.c)-(457/500)*A.s*R.s) := by ring
      _ ≤ 0 := sub_nonpos.mpr ((sub_nonpos.mpr combined).trans scaledMargin')
  exact (not_le_of_gt strict) nonpositive

theorem wall_axis_impossible (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (ac : 0 < A.c) (aNonneg : 0 ≤ A.s) (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (narrow : 12*A.s ≤ 5*A.c) (cross : 0 ≤ A.c*R.s-A.s*R.c)
    (lowerU : 2*A.c+2*A.s ≤ A.loU)
    (lowerV : -(47/20)*A.s+(33/20)*A.c ≤ A.loV)
    (outer : A.Inside (47/20) (53/20))
    (marker : R.Inside (1543/500) 2)
    (axis : upper A R.c R.s ≤ R.loU) : False := by
  let d := A.c*R.c+A.s*R.s
  let k := A.c*R.s-A.s*R.c
  have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos ac rc) (mul_nonneg aNonneg rs)
  have kn : 0 ≤ k := cross
  have formula := (support_formulas A R dp.le cross).1
  change upper A R.c R.s=d*(A.loU+A.side)+k*(A.loV+A.side) at formula
  have lu := mul_le_mul_of_nonneg_left lowerU dp.le
  have lv := mul_le_mul_of_nonneg_left lowerV kn
  have compose : d*(2*A.c+2*A.s)+k*(-(47/20)*A.s+(33/20)*A.c) =
      R.c*X A.c A.s+R.s*Y A.c A.s := by
    dsimp [d,k,X,Y]
    linear_combination (2*R.c+(33/20)*R.s)*A.unit_normal
  have centralBound : R.c*X A.c A.s+R.s*Y A.c A.s+A.side*(d+k) ≤
      upper A R.c R.s := by
    calc
      _ = d*(2*A.c+2*A.s)+k*(-(47/20)*A.s+(33/20)*A.c)+A.side*(d+k) := by
        rw [compose]
      _ ≤ d*A.loU+k*A.loV+A.side*(d+k) :=
        add_le_add_right (add_le_add lu lv) _
      _ = upper A R.c R.s := by rw [formula]; ring
  have wall := CentralWallEscape.right_wall R box
  have markerBound := mul_le_mul_of_nonneg_left marker.2.2.1.le rs
  have wallBound : R.c*R.loU+R.side*R.c+(1543/500)*R.s^2-2*R.c*R.s ≤ 4 := by
    nlinarith only [wall,markerBound]
  have outerBound := (strict_bounds A _ _ R.c R.s R.unit_normal outer).2
  have slopeBound : (13/20)*R.s < (92/125)*R.c := by
    linarith only [outerBound,axis,marker.1]
  let p := A.s/A.c
  let q := R.s/R.c
  let w := 1/R.c
  have pq : p ≤ q := by
    apply (div_le_div_iff₀ ac rc).mpr
    linarith only [cross]
  have qu : q ≤ 23/20 := by
    apply (div_le_iff₀ rc).mpr
    linarith only [slopeBound,rc]
  have angle : A.c*p=A.s := by dsimp [p]; field_simp [ne_of_gt ac]
  have normal : w^2=1+q^2 := by
    dsimp [w,q]
    field_simp [ne_of_gt rc]
    nlinarith only [R.unit_normal]
  have wp : 0 < w := one_div_pos.mpr rc
  have qn : 0 ≤ q := div_nonneg rs rc.le
  have cm := wall_axis_margin A.c A.s p q w
    (cosine_bound A.c A.s ac aNonneg A.unit_normal narrow)
    aNonneg A.unit_normal (div_nonneg aNonneg ac.le) angle pq qu wp.le normal
  let J := w+(A.c-A.s)+q*(A.c+A.s)
  have jp : 0 < J := by
    have product := mul_nonneg qn (add_nonneg ac.le aNonneg)
    dsimp [J]
    linarith only [wp,narrow,ac,product]
  have strict := mul_pos (sub_pos.mpr ha) jp
  have necessary := mul_le_mul_of_nonneg_left
    (le_trans centralBound axis) rc.le
  have identity : R.c^2*(margin A.c A.s q w+(A.side-1)*J) =
      R.c*(R.c*X A.c A.s+R.s*Y A.c A.s+A.side*(d+k))+
      A.side*R.c+(1543/500)*R.s^2-2*R.c*R.s-4 := by
    calc
      _ = R.c*(R.c*X A.c A.s+R.s*Y A.c A.s+A.side*(d+k))+
          A.side*R.c-2*R.c*R.s-4*R.c^2-(457/500)*R.s^2 := by
        dsimp [margin,J,q,w,d,k]
        field_simp [ne_of_gt rc]
        ring
      _ = _ := by nlinarith only [R.unit_normal]
  have positive := mul_pos (sq_pos_of_pos rc) (add_pos_of_nonneg_of_pos cm strict)
  rw [← same] at wallBound
  have nonpositive : R.c*(R.c*X A.c A.s+R.s*Y A.c A.s+A.side*(d+k))+
      A.side*R.c+(1543/500)*R.s^2-2*R.c*R.s-4 ≤ 0 := by
    calc
      _ = R.c*(R.c*X A.c A.s+R.s*Y A.c A.s+A.side*(d+k))+
          (A.side*R.c+(1543/500)*R.s^2-2*R.c*R.s-4) := by ring
      _ ≤ R.c*R.loU+(A.side*R.c+(1543/500)*R.s^2-2*R.c*R.s-4) :=
        add_le_add_right necessary _
      _ = (R.c*R.loU+A.side*R.c+(1543/500)*R.s^2-2*R.c*R.s)-4 := by ring
      _ ≤ 0 := sub_nonpos.mpr wallBound
  rw [← identity] at nonpositive
  exact (not_le_of_gt positive) nonpositive

#print axioms central_axis_impossible
#print axioms wall_axis_impossible
end N12Compact.CentralWallPairSupport
