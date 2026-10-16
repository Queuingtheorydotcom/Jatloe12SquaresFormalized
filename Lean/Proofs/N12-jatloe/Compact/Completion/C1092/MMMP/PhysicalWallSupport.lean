import S12.SquareSupportBase
import Compact.Completion.C1092.WholeSupports

/-! Generic lower supports of one complete physical wall square. The
actual center sign and genuine wall are independent explicit premises. -/
namespace N12Compact.C1092MMMPPhysicalWallSupport
open S12 S12Pilot ABTransverse ThreeSquare
set_option Elab.async false

theorem center_bound (W : OpenSquare) (wh : 0≤W.c) (ws : W.s≤0)
    (wall : ∀ x y, W.Inside x y → x≤2) :
    centerX W+W.side*(W.c-W.s)/2≤2 := by
  have bound := square_support_bound W 1 0 2
    (by intro x y own; simpa only [one_mul,zero_mul,add_zero] using wall x y own)
  norm_num [squareRadius,abs_of_nonneg wh,abs_of_nonpos ws] at bound
  linarith only [bound]

theorem lower_le (W : OpenSquare) (wh : 0≤W.c) (ws : W.s≤0)
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (nx ny : ℝ) (xn : 0≤nx) (yn : ny≤0) :
    lower W nx ny≤2*nx-W.side*(nx*(W.c-W.s)+
      |nx*W.c+ny*W.s|+|-nx*W.s+ny*W.c|)/2 := by
  have wallWeighted := mul_le_mul_of_nonneg_left (center_bound W wh ws wall) xn
  have centerWeighted := mul_nonpos_of_nonpos_of_nonneg yn cut
  dsimp [lower,supportRadius]
  nlinarith only [wallWeighted,centerWeighted]

theorem own_lt (W : OpenSquare) (side : 1<W.side) (wh : 0≤W.c) (ws : W.s≤0)
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W) :
    W.loU<2*W.c-(1+W.c^2-W.c*W.s)/2 := by
  have bound := lower_le W wh ws wall cut W.c W.s wh ws
  rw [(ownU W).1,
    show W.c*W.c+W.s*W.s=1 by nlinarith only [W.unit_normal],
    show -W.c*W.s+W.s*W.c=0 by ring] at bound
  norm_num only [abs_one,abs_zero,add_zero] at bound
  have coefficient : 0<1+W.c^2-W.c*W.s := by
    have product := mul_nonpos_of_nonneg_of_nonpos wh ws
    nlinarith only [sq_nonneg W.c,product]
  have strict := mul_pos (sub_pos.mpr side) coefficient
  nlinarith only [bound,strict]

#print axioms lower_le
#print axioms own_lt
end N12Compact.C1092MMMPPhysicalWallSupport
