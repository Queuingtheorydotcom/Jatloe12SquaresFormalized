import Compact.Completion.C1092.MMMP.BottomBoundaryOrder
import Compact.Completion.C1092.MixedCornerSupports

/-! DOUBLE-RIGHT-BOTTOM-ORIGIN section 3: the actual boundary normal
cannot separate. The paper's half-angle comparison is encoded by its
rational polynomial; the steep-angle sign uses its already established
cosine and sine bounds. No interval is sampled. -/
namespace N12Compact.C1092MMMPBottomBoundaryMargin
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic
open C1092WholeSupports C1092MixedCornerSupports C1092MMMPBottomBoundaryOrder
set_option Elab.async false

private theorem low_scalar {c s b t : ℝ} (cn : Normal c s)
    (sp : 0<s) (bp : 0<b) (tp : 0<t) (unit : b^2+t^2=1)
    (small : C1092WallProfileScalars.half c s<13/50)
    (order : 0<t*c-b*s) (low : 4*t≤3*b) :
    1<b*c+t*s+(t*c-b*s)*((7/20)*(c-s)) := by
  let z := C1092WallProfileScalars.half c s
  let w := C1092WallProfileScalars.half b t
  let q := (7/20)*(c-s)
  let alpha := b*c+t*s
  let delta := t*c-b*s
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have zp : 0<z := div_pos sp (by linarith only [cp])
  have wp : 0<w := div_pos tp (by linarith only [bp])
  have idsC := C1092MMMPPositiveInwardHalfangle.half_identities c s cp cn.2.2
  have idsR := C1092MMMPPositiveInwardHalfangle.half_identities b t bp unit
  have angleC : z*(1+c)=s := idsC.1
  have unitC : s*z=1-c := idsC.2
  have angleR : w*(1+b)=t := idsR.1
  have unitR : t*w=1-b := idsR.2
  have sector := mul_nonneg (show 0≤3*b-4*t by linarith only [low])
    (show 0≤3*b+4*t by linarith only [bp,tp])
  have bLower : 4/5≤b := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<4/5-b by linarith only [bad])
      (show 0<4/5+b by linarith only [bp])
    nlinarith only [product,sector,unit]
  have tUpper : t≤3/5 := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<t-3/5 by linarith only [bad])
      (show 0<t+3/5 by linarith only [tp])
    nlinarith only [product,sector,unit]
  have wUpper : w≤1/3 := by
    have numerator : 3*t≤1+b := by linarith only [bLower,tUpper]
    apply (div_le_iff₀ (show 0<1+b by linarith only [bp])).mpr
    linarith only [numerator]
  have qNonnegative : 0≤q := by dsimp [q]; linarith only [cn.2.1]
  have qUpper : q≤7/20 := by dsimp [q]; linarith only [cb.2.1,cn.1]
  have cosId : c*(1+z^2)=1-z^2 := by
    linear_combination z*angleC+unitC
  have sinId : s*(1+z^2)=2*z := by
    linear_combination z*unitC-angleC
  have identity : (1+z^2)*(q*(3+z)-1+3*z)=
      1/20+(5/4)*z-(11/4)*z^2+(53/20)*z^3 := by
    dsimp [q]
    linear_combination (7/20)*(3+z)*cosId-(7/20)*(3+z)*sinId
  have polynomial : 0<1/20+(5/4)*z-(11/4)*z^2+(53/20)*z^3 := by
    have first := mul_nonneg zp.le
      (show 0≤5/4-(11/4)*z by linarith only [small])
    have last := pow_nonneg zp.le 3
    nlinarith only [first,last]
  have atThird : 0<q*(3+z)-1+3*z := by
    apply pos_of_mul_pos_right (show 0<(1+z^2)*(q*(3+z)-1+3*z) by
      rw [identity]; exact polynomial)
    nlinarith only [sq_nonneg z]
  have qz : q*z≤1 := by
    have bound := mul_le_mul qUpper (show z≤13/50 by linarith only [small])
      zp.le (by norm_num : (0:ℝ)≤7/20)
    linarith only [bound]
  have correction := mul_nonneg (sub_nonneg.mpr wUpper) (sub_nonneg.mpr qz)
  have halfGap : 0<q*(1+z*w)-(w-z) := by
    nlinarith only [atThird,correction]
  have alphaPositive : 0<alpha :=
    add_pos_of_pos_of_nonneg (mul_pos bp cp) (mul_nonneg tp.le cn.1)
  have relative : delta*(1+z*w)=(1+alpha)*(w-z) := by
    dsimp [delta,alpha]
    linear_combination (c*z-s)*unitR+(t-b*w)*unitC+angleC-angleR
  have relativeUnit : alpha^2+delta^2=1 := by
    calc
      _ = (b^2+t^2)*(c^2+s^2) := by dsimp [alpha,delta]; ring
      _ = 1 := by rw [unit,cn.2.2]; norm_num
  have positive := mul_pos (show 0<1+alpha by linarith only [alphaPositive]) halfGap
  have factor : 0<1+z*w := by nlinarith only [mul_pos zp wp]
  have gap : 0<q*(1+alpha)-delta := by
    have scaled : 0<(1+z*w)*(q*(1+alpha)-delta) := by
      nlinarith only [relative,positive]
    exact pos_of_mul_pos_right scaled factor.le
  have scaled := mul_pos order gap
  have answer : 0<alpha+delta*q-1 := by
    have identity : (1+alpha)*(alpha+delta*q-1)=delta*(q*(1+alpha)-delta) := by
      linear_combination relativeUnit
    apply pos_of_mul_pos_right (show 0<(1+alpha)*(alpha+delta*q-1) by
      rw [identity]; exact scaled)
    linarith only [alphaPositive]
  dsimp [alpha,delta,q] at answer
  linarith only [answer]

private theorem high_scalar {c s b t : ℝ} (cn : Normal c s)
    (cosine : 2331/2669<c) (sine : s<1300/2669)
    (bp : 0<b) (high : 3*b≤4*t) :
    (543/500)*b<b*c+t*s+(t*c-b*s)*((7/20)*(c-s)) := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cosine]
  let q := (7/20)*(c-s)
  have qn : 0≤q := by dsimp [q]; linarith only [cn.2.1]
  have coefficient : 0≤s+q*c := add_nonneg cn.1 (mul_nonneg qn cp.le)
  have raised := mul_nonneg (show 0≤t-(3/4)*b by linarith only [high]) coefficient
  have factor : 0≤1-(49/80)*s := by linarith only [sine]
  have first := mul_pos (show 0<c-871/1000 by linarith only [cosine])
    (show 0<1-(49/80)*s by linarith only [sine])
  have last := mul_nonneg cn.1 (by norm_num : (0:ℝ)≤3/4-(49/80)*(871/1000))
  have margin : 0<c+(3/4)*s-543/500+21/80+(7/80)*s^2-(49/80)*s*c := by
    nlinarith only [first,last,sq_nonneg s]
  have strict := mul_pos bp margin
  have identity : b*c+(3/4)*b*s+((3/4)*b*c-b*s)*q-(543/500)*b=
      b*(c+(3/4)*s-543/500+21/80+(7/80)*s^2-(49/80)*s*c) := by
    dsimp [q]
    linear_combination (21/80)*b*cn.2.2
  dsimp [q] at raised identity
  nlinarith only [raised,identity,strict]

private theorem lowerU_lt_one (C R : OpenSquare) (side : 1<R.side) (data : Data C R) :
    R.loU<1 := by
  have bcap : R.c<1 := by
    have square := mul_pos data.sine data.sine
    nlinarith only [square,R.unit_normal,data.cosine,sq_nonneg (R.c-1)]
  by_cases low : R.c≤457/500
  · linarith only [data.markerU,low]
  · have negative := mul_neg_of_neg_of_pos
      (show R.c-1<0 by linarith only [bcap])
      (show 0<(543/500)*R.c-457/500 by linarith only [low])
    have marker := mul_lt_mul_of_pos_left data.markerV data.sine
    have excess := mul_pos data.cosine (sub_pos.mpr side)
    have bound : R.c*R.loU<R.c := by
      nlinarith only [data.wall,marker,excess,negative,R.unit_normal]
    exact (mul_lt_mul_iff_right₀ data.cosine).mp (by simpa only [mul_one] using bound)

/-- Section 3 excludes the boundary square's own upward normal over its
entire first quadrant, including the switching angle t=3b/4. -/
theorem boundary_normal_impossible (C R : OpenSquare) (side : 1<C.side)
    (same : C.side=R.side) (cn : Normal C.c C.s)
    (cosine : 2331/2669<C.c) (sine : C.s<1300/2669)
    (sp : 0<C.s) (small : C1092WallProfileScalars.half C.c C.s<13/50)
    (lower : 0≤C.loU) (M : C.Inside (7/20) (7/20))
    (data : Data C R) (separation : upper C R.c R.s≤R.loU) : False := by
  let alpha := R.c*C.c+R.s*C.s
  let delta := R.s*C.c-R.c*C.s
  let q := (7/20)*(C.c-C.s)
  have cp : 0<C.c := by linarith only [cosine]
  have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos data.cosine cp)
    (mul_nonneg data.sine.le cn.1)
  have dp : 0<delta := data.angle
  have formula := upper_nn C R.c R.s alpha delta rfl (by dsimp [delta]; ring) ap.le dp.le
  have first := mul_pos ap (show 0<C.loU+C.side-1 by linarith only [lower,side])
  have last := mul_pos dp (show 0<C.loV+C.side-q by dsimp [q]; linarith only [M.2.2.2])
  have bound : alpha+delta*q<upper C R.c R.s := by
    rw [formula]
    nlinarith only [first,last]
  by_cases low : 4*R.s≤3*R.c
  · have scalar := low_scalar cn sp data.cosine data.sine R.unit_normal small data.angle low
    have cap := lowerU_lt_one C R (by rwa [←same]) data
    dsimp [alpha,delta,q] at bound
    linarith only [scalar,bound,separation,cap]
  · have scalar := high_scalar cn cosine sine data.cosine (le_of_not_ge low)
    dsimp [alpha,delta,q] at bound
    linarith only [scalar,bound,separation,data.markerU]

#print axioms boundary_normal_impossible
end N12Compact.C1092MMMPBottomBoundaryMargin
