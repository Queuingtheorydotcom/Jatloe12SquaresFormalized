import Compact.Geometry.CentralNegativeNeighborBounds
import Compact.Geometry.C977NegativeCorner

/-! The actual two incoming supports of a negative southeast neighbor
both force the same small central excess. Full congruent side corrections
are retained, and the second neighbor face is explicit when required. -/
namespace N12Compact.CentralNegativeNeighbor

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner CentralNegativeNeighborBounds

theorem own_axis (A B : OpenSquare) (t : ℝ) (signed : B.s=-t)
    (an : Normal A.c A.s) (bn : Normal B.c t)
    (side : 1<B.side) (center : A.Inside 2 2)
    (capU : B.loU+B.side≤3*B.c-t) (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : A.loU+A.side≤lower B A.c A.s) :
    A.s<2/5 ∧ A.loU+A.side≤2*(A.c+A.s)+(9/100)*A.c := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have ac : 0<A.c := by linarith only [ab.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let K := A.c*B.c-A.s*t
  let H := A.c*t+A.s*B.c
  have kp : 0≤K := by
    have first := mul_nonneg bc.le (sub_nonneg.mpr an.2.1)
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg ac.le bn.1) (mul_nonneg an.1 bc.le)
  have formula : lower B A.c A.s=K*B.loU+H*B.loV :=
    lower_negative_pos B t A.c A.s signed kp hp
  have first := mul_nonneg kp (sub_nonneg.mpr capU)
  have last := mul_nonneg hp (sub_nonneg.mpr capV)
  have width := mul_nonneg (add_nonneg kp hp) (sub_nonneg.mpr side.le)
  have identity : K*(3*B.c-t-1)+H*(2*B.c+3*t-1)-2*(A.c+A.s)=
      A.c*(1-B.c)*(1-t)-A.s*(B.c-t+t^2) := by
    dsimp [K,H]
    linear_combination (3*A.c+2*A.s)*bn.2.2
  have bound : A.loU+A.side-2*(A.c+A.s)≤
      A.c*(1-B.c)*(1-t)-A.s*(B.c-t+t^2) := by
    nlinarith only [incoming,formula,first,last,width,identity]
  have coeff := own_coefficients bn
  have cWeight := mul_nonneg ac.le (sub_nonneg.mpr coeff.1)
  have sWeight := mul_nonneg an.1 (sub_nonneg.mpr coeff.2)
  have sharpen : A.loU+A.side-2*(A.c+A.s)≤(4/45)*A.c-A.s/2 := by
    nlinarith only [bound,cWeight,sWeight]
  exact ⟨by nlinarith only [sharpen,center.2.1,ab.2.1],
    by nlinarith only [sharpen,an.1,ac]⟩

theorem neighbor_axis (A B : OpenSquare) (t : ℝ) (signed : B.s=-t)
    (an : Normal A.c A.s) (bn : Normal B.c t)
    (same : A.side=B.side) (side : 1<A.side) (center : A.Inside 2 2)
    (northwest : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (cap : B.loU+B.side≤3*B.c-t)
    (incoming : upper A B.c (-t)≤B.loU) :
    A.s<2/5 ∧ A.loU+A.side≤2*(A.c+A.s)+(9/100)*A.c := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have ac : 0<A.c := by linarith only [ab.1]
  have bc : 0<B.c := by linarith only [bb.1]
  let K := A.c*B.c-A.s*t
  let H := A.c*t+A.s*B.c
  have kp : 0≤K := by
    have first := mul_nonneg bc.le (sub_nonneg.mpr an.2.1)
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg ac.le bn.1) (mul_nonneg an.1 bc.le)
  have formula : upper A B.c (-t)=K*(A.loU+A.side)-H*A.loV := by
    rw [upper_in_bands]
    have u : B.c*A.c+(-t)*A.s=K := by dsimp [K]; ring
    have v : -B.c*A.s+(-t)*A.c=-H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]; ring
  have face := mul_nonneg hp (sub_nonneg.mpr northwest)
  have size := mul_pos (show 0<1+H by linarith only [hp]) (sub_pos.mpr side)
  have identity : 3*B.c-t-1+H*((47/20)*A.c-(33/20)*A.s-1)-K*(2*(A.c+A.s))=
      excess A.c A.s B.c t := by
    dsimp [K,H,excess]
    linear_combination (-(2*B.c-(47/20)*t))*an.2.2
  rw [←same] at cap
  have bound : K*(A.loU+A.side-2*(A.c+A.s))<excess A.c A.s B.c t := by
    clear_value K H
    nlinarith only [incoming,formula,cap,face,size,identity]
  have centerWeight := mul_nonneg kp
    (show 0≤A.loU+A.side-2*(A.c+A.s) by linarith only [center.2.1])
  have positive : 0<excess A.c A.s B.c t := by linarith only [bound,centerWeight]
  have small := small_of_positive an bn positive
  have margin := upper_bound an bn small.le
  have strictK : 0<K := by
    dsimp [K]
    have first := mul_nonneg (sub_nonneg.mpr ab.1) bc.le
    have last := mul_nonneg (show 0≤2/5-A.s by linarith only [small]) bn.1
    nlinarith only [first,last,bn.2.1,bc]
  refine ⟨small,?_⟩
  have scaled : 0<K*(2*(A.c+A.s)+(9/100)*A.c-(A.loU+A.side)) := by
    dsimp [K]
    dsimp [K] at bound
    nlinarith only [bound,margin]
  have gap := pos_of_mul_pos_right scaled strictK.le
  linarith only [gap]

end N12Compact.CentralNegativeNeighbor
