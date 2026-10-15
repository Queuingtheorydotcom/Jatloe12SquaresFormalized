import Compact.Completion.C1092.MMMMPairScalars

/-! The small-angle northwest sign margin uses a factored quadratic on a
closed interval. The endpoint bound is rational and needs no derivatives. -/
namespace N12Compact.C1092MPPMNorthwestSignScalars
open C977CornerCubic
set_option Elab.async false

theorem upper_span {b t : ℝ} (bn : Normal b t) (angle : (1+b)/4<t) :
    b+t-1<(3/4)*t := by
  have bb := normal_bounds bn
  have bp : 0<1+b := by linarith only [bb.1]
  have tp : 0<t := by linarith only [angle,bb.1]
  have product := mul_pos tp (sub_pos.mpr angle)
  have identity : (1+b)*(1-b-t/4)=t*(t-(1+b)/4) := by
    linear_combination -bn.2.2
  have positive : 0<(1+b)*(1-b-t/4) := by rwa [identity]
  have gap := (mul_pos_iff_of_pos_left bp).mp positive
  linarith only [gap]

theorem cap {d r A H : ℝ} (dn : Normal d r) (small : r<7/50) (close : 99/100<d)
    (au : A≤(7/20)*(d-r)) (hl : 1-(7/20)*(d+r)≤H) (hu : H<41/50)
    (norm : 0<A^2+H^2-2*(d-r)*A-2*(d+r)*H+1) : A<1/10 := by
  have db := normal_bounds dn
  have gp : 17/20<d-r := by linarith only [small,close]
  have hlo : 1≤d+r := db.2.2.2.2.1
  have hhi : d+r<57/50 := by linarith only [db.2.1,small]
  apply lt_of_not_ge
  intro al
  let h := d+r
  let g := d-r
  let H0 := 1-(7/20)*h
  have first := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤A-1/10 by linarith only [al])
    (show A+1/10-2*g≤0 by dsimp [g]; linarith only [au,al,gp])
  have last := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤H-H0 by dsimp [H0,h]; linarith only [hl])
    (show H+H0-2*h≤0 by dsimp [H0,h]; linarith only [hl,hu,hlo])
  have firstIdentity :
      (A^2+H^2-2*g*A-2*h*H+1)-
        ((1/10)^2+H^2-2*g*(1/10)-2*h*H+1)=
      (A-1/10)*(A+1/10-2*g) := by ring
  have lastIdentity :
      ((1/10)^2+H^2-2*g*(1/10)-2*h*H+1)-
        ((1/10)^2+H0^2-2*g*(1/10)-2*h*H0+1)=
      (H-H0)*(H+H0-2*h) := by ring
  have endpoint :
      (1/10)^2+H0^2-2*g*(1/10)-2*h*H0+1=
      -3/80+(h-1)*((329/400)*(h+1)-27/10)-(1/5)*(g-17/20) := by
    dsimp [H0]
    ring
  have factor := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤h-1 by dsimp [h]; linarith only [hlo])
    (show (329/400)*(h+1)-27/10≤0 by dsimp [h]; linarith only [hhi])
  have gap := mul_nonneg (by norm_num : (0:ℝ)≤1/5)
    (show 0≤g-17/20 by dsimp [g]; linarith only [gp])
  change 0<A^2+H^2-2*g*A-2*h*H+1 at norm
  linarith only [norm,first,last,firstIdentity,lastIdentity,endpoint,factor,gap]

theorem wall_sine {b t : ℝ} (bn : Normal b t) (sum : 5/4<b+t) : 9/32<t := by
  have bb := normal_bounds bn
  have first := mul_pos (show 0<b+t-5/4 by linarith only [sum])
    (show 0<b+t+5/4 by linarith only [bb.2.2.2.2.1])
  have cross : 9/16<2*b*t := by nlinarith only [first,bn.2.2]
  have last := mul_nonneg bn.1 (sub_nonneg.mpr bb.2.1)
  nlinarith only [cross,last]

theorem wall_margin {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (small : r<7/50) (close : 99/100<d) (sum : 5/4<b+t) :
    0<b*((9/10)*d+(9/50)*r-1)+t*(2/5-(9/10)*r+(9/50)*d) := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have bp : 0<b := by linarith only [bb.1]
  have tb := wall_sine bn sum
  have first := mul_lt_mul_of_pos_left
    (show -(109/1000)<(9/10)*d+(9/50)*r-1 by linarith only [close,dn.1]) bp
  have weak := mul_nonneg (by norm_num : (0:ℝ)≤109/1000)
    (sub_nonneg.mpr bb.2.1)
  have last := mul_lt_mul_of_pos_left
    (show 2261/5000<2/5-(9/10)*r+(9/50)*d by linarith only [small,close])
    (show 0<t by linarith only [tb])
  have scaled := mul_lt_mul_of_pos_left tb (by norm_num : (0:ℝ)<2261/5000)
  nlinarith only [first,weak,last,scaled]

#print axioms cap
#print axioms wall_margin
end N12Compact.C1092MPPMNorthwestSignScalars
