import Compact.Completion.C1092.MPPMInwardFinalOuterOwnedScalars

/-! INWARD-BOTTOM-ANGLE: scalar comparisons on the whole canonical
arcs. The paper's differential chord argument is replaced by a positive
quadratic identity; its endpoint and all relative-angle equalities remain.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal.BottomAngle
open C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

theorem half_identity {c s : ℝ} (cn : Normal c s) : 1-c=s*half c s := by
  have cb := normal_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have zero : (1+c)*(c-1+s*half c s)=0 := by
    linear_combination cn.2.2+s*data.2.2.1
  have relation := (mul_eq_zero.mp zero).resolve_left (by linarith only [cb.1])
  linarith only [relation]

theorem bad_arc {c s : ℝ} (cn : Normal c s)
    (bad : (half c s)^2-2*half c s+1/5≤0) :
    half c s≤1-c+(2/5)*s ∧ 0≤c+s-1-c*s+(2/5)*s^2 ∧ 543/500<c+s := by
  have cb := normal_bounds cn
  have zb := canonical_half_bounds cn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let z := half c s
  have first : (1+z^2)*(1-c+(2/5)*s-z)= -z*(z^2-2*z+1/5) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have weighted := mul_nonpos_of_nonneg_of_nonpos zb.1 bad
  have scaled : 0≤(1+z^2)*(1-c+(2/5)*s-z) := by nlinarith only [first,weighted]
  have q := nonneg_of_mul_nonneg_right scaled (by nlinarith only [sq_nonneg z] : 0<1+z^2)
  have h := half_identity cn
  have identity : c+s-1-c*s+(2/5)*s^2=s*(1-c+(2/5)*s-z) := by
    nlinarith only [h]
  have arc := mul_nonneg cn.1 q
  have low : 1/10<z := by
    apply lt_of_not_ge
    intro no
    have product := mul_nonneg
      (show 0≤1/10-z by linarith only [no])
      (show 0≤2-z-1/10 by linarith only [no])
    nlinarith only [product,bad]
  have square := mul_nonneg zb.1 (show 0≤5/12-z by exact sub_nonneg.mpr zb.2)
  have sumIdentity : (1+z^2)*(c+s-543/500)=2*z-43/500-(1043/500)*z^2 := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have sumScaled : 0<(1+z^2)*(c+s-543/500) := by
    nlinarith only [sumIdentity,square,low]
  have sum := pos_of_mul_pos_right sumScaled (by nlinarith only [sq_nonneg z] : 0≤1+z^2)
  exact ⟨by linarith only [q],by rw [identity]; exact arc,by linarith only [sum]⟩

theorem dot_le_one {c s P Q : ℝ} (cn : Normal c s) (norm : P^2+Q^2≤1) :
    P*c+Q*s≤1 := by
  have identity : (P*c+Q*s)^2+(P*s-Q*c)^2=P^2+Q^2 := by
    linear_combination (P^2+Q^2)*cn.2.2
  nlinarith only [identity,norm,sq_nonneg (P*s-Q*c),sq_nonneg (P*c+Q*s-1)]

theorem positive_central_norm {h k : ℝ} (bn : Normal h k) :
    (1+(43/500)*k^2-(13/50)*h*k)^2+
      ((43/500)*h*k+(13/50)*k^2)^2≤1 := by
  have product := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
  have identity :
      (1+(43/500)*k^2-(13/50)*h*k)^2+
        ((43/500)*h*k+(13/50)*k^2)^2=
      1+(61749/250000)*k^2-(13/25)*h*k := by
    linear_combination ((43/500)^2+(13/50)^2)*k^2*bn.2.2
  nlinarith only [identity,product,sq_nonneg k]

theorem positive_u_margin {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k)
    (sum : 543/500<c+s) :
    0<h*(c^2/2+s)+k*(c-c*s/2-543/500) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  let P := c^2/2+s
  let Q := c-c*s/2-543/500
  have pp : 0<P := by dsimp [P]; nlinarith only [cb.1,cn.1,sq_nonneg (c-7/10)]
  have weighted := mul_nonneg (show 0≤c by linarith only [cb.1]) (sub_nonneg.mpr cn.2.1)
  have together : 0<P+Q := by dsimp [P,Q]; nlinarith only [sum,weighted]
  have first := mul_nonneg (sub_nonneg.mpr bn.2.1) pp.le
  by_cases zero : k=0
  · have strict := mul_pos (show 0<h by linarith only [bb.1]) pp
    dsimp [P,Q] at strict ⊢
    simpa only [zero,zero_mul,add_zero] using strict
  · have strict := mul_pos (lt_of_le_of_ne bn.1 (Ne.symm zero)) together
    dsimp [P,Q] at first strict
    nlinarith only [first,strict]

/-- The entire up-left boundary envelope; no differential inequality
or angular partition is imported. -/
theorem positive_wall_margin {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k)
    (arc : 0≤c+s-1-c*s+(2/5)*s^2) :
    0≤1/2+h^2/2+h*k/2+
      h*(c+s-c*s+(2/5)*s^2-2)+k*(c-s-c^2+(2/5)*c*s) := by
  have cb := normal_bounds cn
  let A := c+s-c*s+(2/5)*s^2
  let B := c-s-c^2+(2/5)*c*s
  have al : 1≤A := by dsimp [A]; linarith only [arc]
  have cross : c*s≤1/2 := by nlinarith only [cn.2.2,sq_nonneg (c-s)]
  have cosine := mul_nonneg (show 0≤c-7/10 by linarith only [cb.1])
    (show 0≤13/10-c by linarith only [cb.2.1])
  have together : 61/100≤A+B := by
    dsimp [A,B]
    nlinarith only [cosine,cross,sq_nonneg s]
  have first := mul_nonneg (sub_nonneg.mpr bn.2.1) (sub_nonneg.mpr al)
  have last := mul_nonneg bn.1 (sub_nonneg.mpr together)
  have middle : 0≤(1-h)^2/2+k*(h/2-39/100) := by
    by_cases sign : 0≤h/2-39/100
    · have product := mul_nonneg bn.1 sign
      nlinarith only [product,sq_nonneg (1-h)]
    · have product := mul_nonneg (sub_nonneg.mpr bn.2.1)
        (show 0≤39/100-h/2 by linarith only [sign])
      nlinarith only [product,sq_nonneg (h-139/200)]
  have identity : 1/2+h^2/2+h*k/2+h*(A-2)+k*B=
      (h-k)*(A-1)+k*(A+B-61/100)+(1-h)^2/2+k*(h/2-39/100) := by ring
  dsimp [A,B] at identity first last
  nlinarith only [identity,first,last,middle]

theorem negative_height {h k a D : ℝ} (bn : Normal h k) (side : 1<a)
    (marker : -(543/500)*h<D)
    (wall : a*h+(543/500)*k^2-2≤h*D) : -1<D := by
  have bb := normal_bounds bn
  by_cases low : h≤10/11
  · linarith only [marker,low]
  · have product := mul_nonneg (show 0≤1-h by linarith only [bb.2.1])
      (show 0≤(543/500)*(1+h)-2 by linarith only [low])
    have strict := mul_pos (show 0<h by linarith only [bb.1]) (sub_pos.mpr side)
    have scaled : 0<h*(D+1) := by nlinarith only [product,strict,wall,bn.2.2]
    have result := pos_of_mul_pos_right scaled (by linarith only [bb.1] : 0≤h)
    linarith only [result]

theorem relative_unit {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k) :
    (c*h+s*k)^2+(c*k-s*h)^2=1 := by
  linear_combination (h^2+k^2)*cn.2.2+bn.2.2

theorem relative_dot_lower {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k)
    (order : s*h≤c*k) : h≤c*h+s*k := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  have hi := half_identity cn
  let z := half c s
  have nonnegative := mul_nonneg (show 0≤h by linarith only [bb.1]) data.1
  have scaledIdentity : c*(k-h*z)=(c*k-s*h)+h*z := by
    linear_combination -h*data.2.2.1
  have scaled : 0≤c*(k-h*z) := by
    nlinarith only [order,nonnegative,scaledIdentity]
  have rest := nonneg_of_mul_nonneg_right scaled (by linarith only [cb.1] : 0<c)
  have product := mul_nonneg cn.1 rest
  have identity : c*h+s*k-h=s*(k-h*z) := by
    linear_combination -h*hi
  nlinarith only [identity,product]

theorem negative_before_margin {c s h k Q : ℝ} (cn : Normal c s) (bn : Normal h k)
    (order : c*k≤s*h) (qlow : half c s≤Q) :
    1≤c*h+s*k+Q*(s*h-c*k) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have dot := relative_dot_lower bn cn (by nlinarith only [order])
  have data := quarter_data c s (by linarith only [cb.1]) cn.1 cn.2.2
  let L := c*h+s*k
  let e := s*h-c*k
  let z := half c s
  have en : 0≤e := by dsimp [e]; linarith only [order]
  have upper : e≤s := by
    have first := mul_nonneg cn.1 (show 0≤1-h by linarith only [bb.2.1])
    have last := mul_nonneg (show 0≤c by linarith only [cb.1]) bn.1
    dsimp [e]; nlinarith only [first,last]
  have weighted := mul_nonneg data.1 (show 0≤L-c by dsimp [L]; nlinarith only [dot])
  have factor : 0≤z*(1+L)-e := by nlinarith only [weighted,data.2.2.1,upper]
  have identity : (L+z*e-1)*(1+L)=e*(z*(1+L)-e) := by
    have unit := relative_unit cn bn
    dsimp [L,e]
    nlinarith only [unit]
  have product := mul_nonneg en factor
  have scaled : 0≤(L+z*e-1)*(1+L) := by rw [identity]; exact product
  have value := nonneg_of_mul_nonneg_left scaled (by dsimp [L]; nlinarith only [dot,cb.1] : 0<1+L)
  have extra := mul_nonneg (sub_nonneg.mpr qlow) en
  dsimp [L,e,z] at value extra
  nlinarith only [value,extra]

theorem negative_after_margin {c s h k : ℝ} (cn : Normal c s) (bn : Normal h k)
    (order : s*h≤c*k) : 1≤c*h+s*k+(c/2)*(c*k-s*h) := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have dot := relative_dot_lower cn bn order
  have square := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤h+k by linarith only [bb.1,bn.1])
  have small : k<71/100 := by nlinarith only [bn.2.2,square,bn.1,sq_nonneg (k-71/100)]
  let L := c*h+s*k
  let e := c*k-s*h
  have en : 0≤e := by dsimp [e]; linarith only [order]
  have upper : e≤c*k := by
    have product := mul_nonneg cn.1 (show 0≤h by linarith only [bb.1])
    dsimp [e]; nlinarith only [product]
  have product := mul_nonneg (show 0≤c by linarith only [cb.1])
    (show 0≤1+L-2*k by dsimp [L]; linarith only [dot,bb.1,small])
  have factor : 0≤(c/2)*(1+L)-e := by nlinarith only [product,upper]
  have identity : (L+(c/2)*e-1)*(1+L)=e*((c/2)*(1+L)-e) := by
    have unit := relative_unit cn bn
    dsimp [L,e]
    nlinarith only [unit]
  have weighted := mul_nonneg en factor
  have scaled : 0≤(L+(c/2)*e-1)*(1+L) := by rw [identity]; exact weighted
  have value := nonneg_of_mul_nonneg_left scaled (by dsimp [L]; linarith only [dot,bb.1] : 0<1+L)
  dsimp [L,e] at value
  linarith only [value]

theorem negative_central_norm {h k : ℝ} (bn : Normal h k) (steep : (14/25)*h≤k) :
    (1+(43/500)*h^2-(14/25)*h*k)^2+
      ((14/25)*h^2+(43/500)*h*k)^2<1 := by
  have bb := normal_bounds bn
  have product := mul_nonneg (show 0≤h by linarith only [bb.1]) (sub_nonneg.mpr steep)
  have identity :
      (1+(43/500)*h^2-(14/25)*h*k)^2+
        ((14/25)*h^2+(43/500)*h*k)^2=
      1+(123249/250000)*h^2-(28/25)*h*k := by
    linear_combination ((43/500)^2+(14/25)^2)*h^2*bn.2.2
  nlinarith only [identity,product,bb.1,sq_nonneg (h-7/10)]

theorem threshold {c s : ℝ} (cn : Normal c s)
    (polynomial : 0<(half c s)^2-2*half c s+1/5) :
    half c s<1-2*Real.sqrt 5/5 ∧ half c s<53/500 := by
  have zb := canonical_half_bounds cn
  let z := half c s
  have rootPositive : 0<Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have rootSquare : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  constructor
  · apply lt_of_not_ge
    intro no
    have product := mul_nonneg
      (show 0≤2*Real.sqrt 5/5-(1-z) by linarith only [no])
      (show 0≤2*Real.sqrt 5/5+(1-z) by linarith only [rootPositive,zb.2])
    nlinarith only [product,rootSquare,polynomial]
  · apply lt_of_not_ge
    intro no
    have product := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤z-53/500 by exact sub_nonneg.mpr no)
      (show z+53/500-2≤0 by linarith only [zb.2])
    nlinarith only [product,polynomial]

#print axioms positive_wall_margin
#print axioms negative_before_margin
#print axioms negative_after_margin
end N12Compact.C1092MPPMInwardFinal.BottomAngle
