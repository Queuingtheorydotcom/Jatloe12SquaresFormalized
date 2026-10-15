import Compact.Completion.C981.AngularScalars

/-! Exact scalar bounds for the last two C981 cycles at the thirty-degree
threshold. The rational enclosing tangent replaces monotonic derivatives. -/
namespace N12Compact.C981CompletionLastScalars
open C977CornerCubic
set_option Elab.async false

theorem half_endpoint_refined {b t F G : ℝ} (normal : Normal b t)
    (angle : 1/2 ≤ t) (fp : 43/50 ≤ F) (gc : G ≤ 41/100) :
    b*F+t*G ≤ (751/867)*F+G/2 := by
  have bounds := normal_bounds normal
  have support : 867*b+500*t ≤ 1001 := by
    have identity : (867*b+500*t)^2+(500*b-867*t)^2=
        1001689*(b^2+t^2) := by ring
    rw [normal.2.2] at identity
    nlinarith only [identity,sq_nonneg (500*b-867*t),sq_nonneg (867*b+500*t-1001)]
  have order : 0 ≤ 500*F-867*G := by linarith only [fp,gc]
  have first := mul_nonneg (show 0 ≤ F by linarith only [fp])
    (show 0 ≤ 1001-867*b-500*t by linarith only [support])
  have last := mul_nonneg (sub_nonneg.mpr angle) order
  have endpoint : b*F+t*G ≤ (751/867)*F+G/2 := by
    nlinarith only [first,last]
  exact endpoint

theorem half_endpoint {b t F G : ℝ} (normal : Normal b t)
    (angle : 1/2 ≤ t) (fp : 43/50 ≤ F) (gc : G ≤ 41/100) :
    b*F+t*G ≤ (867/1000)*F+G/2 := by
  have endpoint := half_endpoint_refined normal angle fp gc
  linarith only [endpoint,fp]

theorem marker_cut_small {d r b t : ℝ} (cn : Normal d r) (bn : Normal b t)
    (cut : 1 < b*(1-r*(1-(7/20)*(d+r)))+t*(1-d*(1-(7/20)*(d+r)))) :
    r < 7/50 ∧ 99/100 < d := by
  classical
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have dp : 0 < d := by linarith only [cb.1]
  have bp : 0 < b := by linarith only [bb.1]
  let H := d+r
  let q := 1-(7/20)*H
  let F := 1-r*q
  let G := 1-d*q
  change 1 < b*F+t*G at cut
  have Hlow : 1 ≤ H := cb.2.2.2.2.1
  have Hhigh : H ≤ 10/7 := cb.2.2.2.2.2
  have normIdentity : (b*F+t*G)^2+(b*G-t*F)^2=(b^2+t^2)*(F^2+G^2) := by ring
  rw [bn.2.2,one_mul] at normIdentity
  have positiveSquare := mul_pos (sub_pos.mpr cut)
    (show 0 < b*F+t*G+1 by linarith only [cut])
  have normLarge : 1 < F^2+G^2 := by
    nlinarith only [normIdentity,positiveSquare,sq_nonneg (b*G-t*F)]
  have polynomial : F^2+G^2-1=2-(27/10)*H+(329/400)*H^2 := by
    calc
      _ = 1-2*(d+r)*q+(d^2+r^2)*q^2 := by dsimp [F,G]; ring
      _ = _ := by rw [cn.2.2]; dsimp [H,q]; ring
  have Hsmall : H < 113/100 := by
    apply lt_of_not_ge
    intro large
    have coefficient : -(27/10)+(329/400)*(H+113/100) ≤ 0 := by
      linarith only [Hhigh]
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ H-113/100 by linarith only [large]) coefficient
    have identity :
        2-(27/10)*H+(329/400)*H^2 = -(2999/4000000)+
          (H-113/100)*(-(27/10)+(329/400)*(H+113/100)) := by ring
    have negative : F^2+G^2-1 < 0 := by
      rw [polynomial, identity]
      calc
        _ ≤ -(2999/4000000)+0 := add_le_add_left product _
        _ < 0 := by norm_num
    exact (sub_pos.mpr normLarge).not_le negative.le
  have rSmall : r < 7/50 := by
    apply lt_of_not_ge
    intro large
    have rHalf : r < 113/200 := by dsimp [H] at Hsmall; linarith only [Hsmall,cn.2.1]
    have comparison := mul_nonneg
      (show 0 ≤ 113/100-r-d by dsimp [H] at Hsmall; linarith only [Hsmall])
      (show 0 ≤ 113/100-r+d by linarith only [rHalf,dp])
    have interval := mul_nonneg (show 0 ≤ r-7/50 by linarith only [large])
      (show 0 ≤ 99/100-r by linarith only [rHalf])
    nlinarith only [comparison,interval,cn.2.2]
  have dLarge : 99/100 < d := by
    apply lt_of_not_ge
    intro small
    have comparison := mul_nonneg (show 0 ≤ 99/100-d by linarith only [small])
      (show 0 ≤ 99/100+d by linarith only [dp])
    have sine := mul_pos (show 0 < 7/50-r by linarith only [rSmall])
      (show 0 < 7/50+r by linarith only [cn.1])
    nlinarith only [comparison,sine,cn.2.2]
  exact ⟨rSmall,dLarge⟩

theorem negative_impossible (d r b t : ℝ) (cn : Normal d r) (bn : Normal b t)
    (angle : 1/2 ≤ t)
    (markerCut : 1 < b*(1-r*(1-(7/20)*(d+r)))+t*(1-d*(1-(7/20)*(d+r))))
    (pointCut : 1 < b*(1-r+(13/50)*d*r+r^2)+t*(1-d+(13/50)*d^2+d*r)) :
    False := by
  have cb := normal_bounds cn
  have ⟨rs,dl⟩ := marker_cut_small cn bn markerCut
  have cross := mul_nonneg (show 0 ≤ d by linarith only [cb.1]) cn.1
  have defect : 1-d ≤ (3/5)*r^2 := by
    have product := mul_nonneg (sub_nonneg.mpr cb.2.1)
      (show 0 ≤ 3*d-2 by linarith only [dl])
    nlinarith only [product,cn.2.2]
  have square : r^2 ≤ 49/2500 := by
    have product := mul_nonneg (show 0 ≤ 7/50-r by linarith only [rs])
      (show 0 ≤ 7/50+r by linarith only [cn.1])
    nlinarith only [product]
  have dr := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
  let F := 1-r+(13/50)*d*r+r^2
  let G := 1-d+(13/50)*d^2+d*r
  have fp : 43/50 ≤ F := by dsimp [F]; nlinarith only [rs,cross,sq_nonneg r]
  have fu : F ≤ 1-(37/50)*r+r^2 := by dsimp [F]; nlinarith only [dr]
  have gu : G ≤ 13/50+r+(17/50)*r^2 := by
    dsimp [G]; nlinarith only [defect,dr,cn.2.2]
  have gc : G ≤ 41/100 := by linarith only [gu,rs,square]
  have endpoint := half_endpoint bn angle fp gc
  have span := mul_nonneg cn.1 (show 0 ≤ 7/50-r by linarith only [rs])
  have last : (867/1000)*F+G/2 < 1 := by
    nlinarith only [fu,gu,span,rs,cn.1]
  change 1 < b*F+t*G at pointCut
  exact (not_lt_of_ge (le_trans endpoint last.le)) pointCut

#print axioms negative_impossible
end N12Compact.C981CompletionLastScalars
