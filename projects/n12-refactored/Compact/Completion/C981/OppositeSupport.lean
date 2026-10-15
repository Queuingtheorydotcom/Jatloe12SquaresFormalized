import Compact.Completion.C981.LastPositivePair

/-! Uniform positive-normal support comparisons for the opposite central
angle argument. Component order and signed coefficients replace the
derivative comparisons in C981-OPPOSITE-CENTRAL-ANGLE Sections2.2--2.3. -/
namespace N12Compact.C981CompletionOppositeSupport

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic
open C981CompletionSupportForms
set_option Elab.async false

theorem cross_order (c s d r : ℝ) (hc : 0 < c) (hs : 0 ≤ s)
    (hd : 0 < d) (hr : 0 ≤ r) (first : c^2+s^2=1) (second : d^2+r^2=1)
    (order : 0 ≤ s*d-c*r) : c ≤ d ∧ r ≤ s := by
  have product := mul_nonneg order
    (add_nonneg (mul_nonneg hs hd.le) (mul_nonneg hc.le hr))
  have identity : (s*d-c*r)*(s*d+c*r)=d^2-c^2 := by
    linear_combination d^2*first-c^2*second
  have cosine : c ≤ d := by
    apply le_of_not_gt
    intro no
    have bad := mul_pos (sub_pos.mpr no) (add_pos hc hd)
    nlinarith only [product,identity,bad]
  have sine : r ≤ s := by
    apply le_of_not_gt
    intro no
    have bad := mul_pos (sub_pos.mpr no) (show 0 < r+s by linarith only [no,hs])
    have cos := mul_nonneg (sub_nonneg.mpr cosine) (add_nonneg hc.le hd.le)
    nlinarith only [bad,cos,first,second]
  exact ⟨cosine,sine⟩

theorem large_bounds {d r : ℝ} (normal : Normal d r) (large : 8/25 ≤ r) :
    d < 237/250 ∧ 1267/1000 < d+r ∧ 32/625 ≤ 1-d := by
  have bounds := normal_bounds normal
  have square := mul_nonneg (sub_nonneg.mpr large)
    (show 0 ≤ r+8/25 by linarith only [normal.1])
  have cosine : d < 237/250 := by
    nlinarith only [square,normal.2.2,sq_nonneg (d-237/250)]
  have sum : 1267/1000 < d+r := by
    apply lt_of_not_ge
    intro no
    have rHigh : r ≤ 1267/2000 := by linarith only [no,normal.2.1]
    have compare := mul_nonneg
      (show 0 ≤ 1267/1000-r-d by linarith only [no])
      (show 0 ≤ 1267/1000-r+d by linarith only [rHigh,bounds.1])
    have interval := mul_nonneg (sub_nonneg.mpr large)
      (show 0 ≤ 947/1000-r by linarith only [rHigh])
    nlinarith only [compare,interval,normal.2.2]
  have defect : 32/625 ≤ 1-d := by
    nlinarith only [square,normal.2.2,sq_nonneg (d-1)]
  exact ⟨cosine,sum,defect⟩

private theorem upper_formula (C : OpenSquare) (r c s : ℝ) (cs : C.s=r)
    (alpha : 0 ≤ c*C.c+s*r) :
    upper C c s=(c*C.c+s*r)*(C.loU+C.side/2)+
      (s*C.c-c*r)*(C.loV+C.side/2)+
      (C.side/2)*(c*C.c+s*r+|s*C.c-c*r|) := by
  rw [upper_in_bands,cs]
  rw [show -c*r+s*C.c=s*C.c-c*r by ring]
  rw [abs_of_nonneg alpha]

theorem floor_upper (C : OpenSquare) (r c s : ℝ) (cs : C.s=r)
    (cn : Normal C.c r) (side : 1 < C.side) (cap : C.side ≤ 1001/1000)
    (large : 8/25 ≤ r) (hc : 0 < c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (floor : -C.c ≤ C.loU) (west : C.Inside (-(1/2)) 0)
    (bottom : C.Inside 0 (-(1/2))) : C.side-C.c ≤ upper C c s := by
  have bounds := normal_bounds cn
  have dp : 0 < C.c := by linarith only [bounds.1]
  have rp : 0 < r := by linarith only [large]
  have defect := (large_bounds cn large).2.2
  let alpha := c*C.c+s*r
  let beta := s*C.c-c*r
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos hc dp,mul_nonneg hs cn.1]
  have formula := upper_formula C r c s cs (by dsimp [alpha] at ap; exact ap.le)
  have uWeight := mul_nonneg ap.le (sub_nonneg.mpr floor)
  by_cases order : 0 ≤ beta
  · have coordinates := cross_order c s C.c r hc hs dp cn.1 unit cn.2.2
      (by simpa only [beta] using order)
    have own := west.2.2.2
    rw [cs] at own
    have vWeight := mul_nonneg order
      (show 0 ≤ C.loV+C.side-r/2 by linarith only [own])
    rw [show |s*C.c-c*r|=beta by exact abs_of_nonneg order] at formula
    let X := C.side*C.c-1+r^2/2
    let Y := C.side*r-C.c*r/2
    have identity : alpha*(C.side-C.c)+beta*(r/2)=c*X+s*Y := by
      dsimp [alpha,beta,X,Y]
      linear_combination -c*cn.2.2
    have first : upper C c s ≥ c*X+s*Y := by
      dsimp [alpha,beta,X,Y] at uWeight vWeight identity ⊢
      nlinarith only [formula,uWeight,vWeight,identity]
    have defectSquare := mul_nonneg (show 0 ≤ 1-C.c-32/625 by linarith only [defect])
      (show 0 ≤ 1-C.c+32/625 by linarith only [bounds.2.1])
    have capWeight := mul_nonneg dp.le (show 0 ≤ 1001/1000-C.side by linarith only [cap])
    have xn : X ≤ 0 := by
      dsimp [X]
      nlinarith only [defectSquare,capWeight,cn.2.2,bounds.2.1]
    have yp : 0 ≤ Y := by
      have coefficient : 0 ≤ C.side-C.c/2 := by linarith only [side,bounds.2.1]
      have product := mul_nonneg cn.1 coefficient
      dsimp [Y]
      nlinarith only [product]
    have cosineWeight := mul_nonneg_of_nonpos_of_nonpos
      (show c-C.c ≤ 0 by linarith only [coordinates.1]) xn
    have sineWeight := mul_nonneg (sub_nonneg.mpr coordinates.2) yp
    have identity : C.c*X+r*Y=C.side-C.c := by
      dsimp [X,Y]
      linear_combination C.side*cn.2.2
    nlinarith only [first,cosineWeight,sineWeight,identity]
  · have negative : beta ≤ 0 := le_of_lt (lt_of_not_ge order)
    have coordinates := cross_order C.c r c s dp cn.1 hc hs cn.2.2 unit
      (by dsimp [beta] at negative; linarith only [negative])
    have own := bottom.2.2.1
    rw [cs] at own
    have vWeight := mul_nonneg (neg_nonneg.mpr negative)
      (show 0 ≤ -C.c/2-C.loV by linarith only [own])
    rw [show |s*C.c-c*r| = -beta by exact abs_of_nonpos negative] at formula
    let X := C.side*C.c-C.c^2+C.c*r/2
    let Y := C.side*r-r*C.c-C.c^2/2
    have first : upper C c s ≥ c*X+s*Y := by
      dsimp [alpha,beta,X,Y] at uWeight vWeight ⊢
      nlinarith only [formula,uWeight,vWeight]
    have xp : 0 ≤ X := by
      have one := mul_nonneg dp.le
        (show 0 ≤ C.side-C.c by linarith only [side,bounds.2.1])
      have two := mul_nonneg dp.le cn.1
      dsimp [X]
      nlinarith only [one,two]
    have yn : Y ≤ 0 := by
      have one := mul_nonneg (sub_nonneg.mpr cn.2.1)
        (show 0 ≤ C.side-C.c by linarith only [side,bounds.2.1])
      have two := mul_nonpos_of_nonneg_of_nonpos dp.le
        (show C.side-(3/2)*C.c ≤ 0 by linarith only [cap,bounds.1])
      dsimp [Y]
      nlinarith only [one,two]
    have cosineWeight := mul_nonneg (sub_nonneg.mpr coordinates.1) xp
    have sineWeight := mul_nonneg_of_nonpos_of_nonpos
      (show s-r ≤ 0 by linarith only [coordinates.2]) yn
    have identity : C.c*X+r*Y=C.side-C.c := by
      dsimp [X,Y]
      linear_combination (C.side-C.c)*cn.2.2
    nlinarith only [first,cosineWeight,sineWeight,identity]

theorem wall_upper (C : OpenSquare) (r c s : ℝ) (cs : C.s=r)
    (cn : Normal C.c r) (side : 1 < C.side) (cap : C.side ≤ 1001/1000)
    (large : 8/25 ≤ r) (hc : 0 < c) (hs : 0 ≤ s) (unit : c^2+s^2=1)
    (left : -1 ≤ C.c*C.loU-r*(C.loV+C.side))
    (bottom : -1 ≤ r*C.loU+C.c*C.loV) : 17/500 < upper C c s := by
  have bounds := normal_bounds cn
  have ⟨dSmall,hLarge,defect⟩ := large_bounds cn large
  have dp : 0 < C.c := by linarith only [bounds.1]
  let alpha := c*C.c+s*r
  let beta := s*C.c-c*r
  let H := C.c+r
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos hc dp,mul_nonneg hs cn.1]
  have formula := upper_formula C r c s cs (by dsimp [alpha] at ap; exact ap.le)
  have centerXLow : C.side*H/2-1 ≤ centerX C := by
    dsimp [centerX,H]
    rw [cs]
    nlinarith only [left]
  have centerYLow : C.side*H/2-1 ≤ centerY C := by
    dsimp [centerY,H]
    rw [cs]
    nlinarith only [bottom]
  have cx := mul_nonneg hc.le (sub_nonneg.mpr centerXLow)
  have cy := mul_nonneg hs (sub_nonneg.mpr centerYLow)
  have base : 17/500 < C.side*(1+C.c*r)-H := by
    have cross := mul_nonneg dp.le cn.1
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < 1+C.c*r by linarith only [cross])
    have square := mul_pos
      (show 0 < H-1-267/1000 by dsimp [H]; linarith only [hLarge])
      (show 0 < H-1+267/1000 by dsimp [H]; linarith only [hLarge])
    dsimp [H] at square ⊢
    nlinarith only [strict,square,cn.2.2]
  have support : C.side*(1+C.c*r)-H ≤ upper C c s := by
    by_cases order : 0 ≤ beta
    · have coordinates := cross_order c s C.c r hc hs dp cn.1 unit cn.2.2
        (by simpa only [beta] using order)
      rw [show |s*C.c-c*r|=beta by exact abs_of_nonneg order] at formula
      let X := C.side*C.c-1
      let Y := C.side*H-1
      have first : c*X+s*Y ≤ upper C c s := by
        dsimp [centerX,centerY] at cx cy
        rw [cs] at cx cy
        dsimp [H,alpha,beta,X,Y] at cx cy ⊢
        nlinarith only [formula,cx,cy]
      have capWeight := mul_nonneg dp.le (show 0 ≤ 1001/1000-C.side by linarith only [cap])
      have xn : X ≤ 0 := by dsimp [X]; nlinarith only [capWeight,dSmall]
      have yp : 0 ≤ Y := by
        have strict := mul_pos (sub_pos.mpr side)
          (show 0 < H by dsimp [H]; linarith only [bounds.2.2.2.2.1])
        dsimp [Y,H] at strict ⊢
        nlinarith only [strict,bounds.2.2.2.2.1]
      have xWeight := mul_nonneg_of_nonpos_of_nonpos
        (show c-C.c ≤ 0 by linarith only [coordinates.1]) xn
      have yWeight := mul_nonneg (sub_nonneg.mpr coordinates.2) yp
      have identity : C.c*X+r*Y=C.side*(1+C.c*r)-H := by
        dsimp [X,Y,H]
        linear_combination C.side*cn.2.2
      nlinarith only [first,xWeight,yWeight,identity]
    · have negative : beta ≤ 0 := le_of_lt (lt_of_not_ge order)
      have coordinates := cross_order C.c r c s dp cn.1 hc hs cn.2.2 unit
        (by dsimp [beta] at negative; linarith only [negative])
      rw [show |s*C.c-c*r| = -beta by exact abs_of_nonpos negative] at formula
      let X := C.side*H-1
      let Y := C.side*r-1
      have first : c*X+s*Y ≤ upper C c s := by
        dsimp [centerX,centerY] at cx cy
        rw [cs] at cx cy
        dsimp [H,alpha,beta,X,Y] at cx cy ⊢
        nlinarith only [formula,cx,cy]
      have xp : 0 ≤ X := by
        have strict := mul_pos (sub_pos.mpr side)
          (show 0 < H by dsimp [H]; linarith only [bounds.2.2.2.2.1])
        dsimp [X,H] at strict ⊢
        nlinarith only [strict,bounds.2.2.2.2.1]
      have rHigh : r ≤ 5/7 := by linarith only [cn.2.1,bounds.2.2.2.2.2]
      have capWeight := mul_nonneg cn.1 (show 0 ≤ 1001/1000-C.side by linarith only [cap])
      have yn : Y ≤ 0 := by dsimp [Y]; nlinarith only [capWeight,rHigh]
      have xWeight := mul_nonneg (sub_nonneg.mpr coordinates.1) xp
      have yWeight := mul_nonneg_of_nonpos_of_nonpos
        (show s-r ≤ 0 by linarith only [coordinates.2]) yn
      have identity : C.c*X+r*Y=C.side*(1+C.c*r)-H := by
        dsimp [X,Y,H]
        linear_combination C.side*cn.2.2
      nlinarith only [first,xWeight,yWeight,identity]
  exact lt_of_lt_of_le base support

#print axioms floor_upper
#print axioms wall_upper
end N12Compact.C981CompletionOppositeSupport
