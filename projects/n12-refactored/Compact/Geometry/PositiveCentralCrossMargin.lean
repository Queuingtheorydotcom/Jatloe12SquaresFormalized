import Compact.Geometry.C977CornerSectorBounds

/-! The two-angle support comparison for the missing-west entrance.
The minimum occurs when the two normals agree. On either side, an exact
divided-difference identity has nonnegative factors; no angle grid or
derivative argument is required. -/
namespace N12Compact.PositiveCentralCrossMargin

open C977CornerCubic C977CornerSectorBounds

noncomputable def F (p q l r : ℝ) : ℝ :=
  1-2*r-(457/500)*q*r/p+r/p+(p*l+q*r)+max (q*l-p*r) 0

private theorem scaled_difference {p q l r : ℝ}
    (on : Normal p q) (ln : Normal l r) :
    p*l*(p+l)*(F p q l r-(2-2*r+r*(1-(457/500)*r)/l)) =
      (p*r-l*q)*(r*(457/500-r)*(p+l)-l*(r-q)*(p-r))+
        p*l*(p+l)*max (q*l-p*r) 0 := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [ob.1]
  have lp : 0<l := by linarith only [lb.1]
  have first :
      p*l*(F p q l r-(2-2*r+r*(1-(457/500)*r)/l)) =
        p*l*(p*l+q*r-1)+r*(l-p)+(457/500)*r*(p*r-l*q)+
          p*l*max (q*l-p*r) 0 := by
    dsimp [F]
    field_simp [ne_of_gt pp,ne_of_gt lp] <;> ring
  calc
    _ = (p+l)*(p*l*(p*l+q*r-1)+r*(l-p)+
        (457/500)*r*(p*r-l*q)+p*l*max (q*l-p*r) 0) := by
      rw [show p*l*(p+l)*
        (F p q l r-(2-2*r+r*(1-(457/500)*r)/l)) =
        (p+l)*(p*l*(F p q l r-(2-2*r+r*(1-(457/500)*r)/l))) by ring]
      rw [first]
    _ = _ := by
      linear_combination l^2*(p-r)*on.2.2+p^2*(l+r)*ln.2.2

/-- Agreement of the two normals minimizes this support expression,
over the entire canonical quarter arc, including its axis endpoints. -/
theorem diagonal_minimum {p q l r : ℝ}
    (on : Normal p q) (ln : Normal l r) :
    2-2*r+r*(1-(457/500)*r)/l ≤ F p q l r := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [ob.1]
  have lp : 0<l := by linarith only [lb.1]
  have sumpos : 0<p+l := add_pos pp lp
  have scale := mul_pos (mul_pos pp lp) sumpos
  have identity := scaled_difference on ln
  have scaled : 0≤p*l*(p+l)*
      (F p q l r-(2-2*r+r*(1-(457/500)*r)/l)) := by
    rcases le_total q r with order | order
    · have cosine : l≤p := cosine_order ln on order
      have sine : r≤5/7 := by linarith only [ln.2.1,lb.2.2.2.2.2]
      have gap := sub_nonneg.mpr order
      have cross : 0≤p*r-l*q := by
        have a := mul_nonneg pp.le gap
        have b := mul_nonneg on.1 (sub_nonneg.mpr cosine)
        nlinarith only [a,b]
      have vanishes : max (q*l-p*r) 0=0 :=
        max_eq_right (by linarith only [cross])
      rw [vanishes] at identity
      have first := mul_nonneg (mul_nonneg lp.le gap)
        (sub_nonneg.mpr ob.2.1)
      have second := mul_nonneg (mul_nonneg lp.le on.1)
        (sub_nonneg.mpr lb.2.2.2.1)
      have third := mul_nonneg
        (mul_nonneg (sub_nonneg.mpr cosine) ln.1)
        (sub_nonneg.mpr lb.2.2.2.1)
      have fourth := mul_nonneg (mul_nonneg ln.1 sumpos.le)
        (show 0≤2*(457/500)-(1+r) by linarith only [sine])
      have bracket : 0≤r*(457/500-r)*(p+l)-l*(r-q)*(p-r) := by
        nlinarith only [first,second,third,fourth]
      have product := mul_nonneg cross bracket
      nlinarith only [identity,product]
    · have cosine : p≤l := cosine_order on ln order
      have gap := sub_nonneg.mpr order
      have cross : 0≤q*l-p*r := by
        have a := mul_nonneg lp.le gap
        have b := mul_nonneg ln.1 (sub_nonneg.mpr cosine)
        nlinarith only [a,b]
      have active : max (q*l-p*r) 0=q*l-p*r := max_eq_left cross
      rw [active] at identity
      have first := mul_nonneg pp.le
        (show 0≤l-q by linarith only [cosine,on.2.1])
      have second := mul_nonneg ln.1
        (show 0≤p+q-457/500 by linarith only [ob.2.2.2.2.1])
      have third := mul_nonneg (mul_nonneg pp.le gap)
        (show 0≤p-r by linarith only [order,on.2.1])
      have bracket : 0≤(p+l)*(p*l-(457/500)*r+r^2)-l*(q-r)*(p-r) := by
        have product := mul_nonneg sumpos.le (add_nonneg first second)
        nlinarith only [product,third]
      have product := mul_nonneg cross bracket
      nlinarith only [identity,product]
  have gap := nonneg_of_mul_nonneg_right scaled scale
  linarith only [gap]

/-- The diagonal endpoint itself has a nonnegative factorization.
This is the exact scalar margin consumed by the geometric entrance. -/
theorem margin {p q l r : ℝ} (on : Normal p q) (ln : Normal l r) :
    2*l*(l+r-1)≤r*F p q l r := by
  have lb := normal_bounds ln
  have lp : 0<l := by linarith only [lb.1]
  have endpoint := diagonal_minimum on ln
  have weighted := mul_nonneg ln.1 (sub_nonneg.mpr endpoint)
  have identity :
      l*(1+l)*(r*(2-2*r+r*(1-(457/500)*r)/l)-2*l*(l+r-1)) =
        (1-l)*r^2*(1-r)+(43/500)*r^3*(1+l) := by
    calc
      _ = (1+l)*(2*l*r-2*l*r^2+r^2-(457/500)*r^3-
          2*l^2*(l+r-1)) := by
        field_simp [ne_of_gt lp] <;> ring
      _ = _ := by linear_combination -2*l*(l+r)*ln.2.2
  have first := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr lb.2.1) (sq_nonneg r))
    (sub_nonneg.mpr lb.2.2.2.1)
  have second : 0≤(43/500 : ℝ)*r^3*(1+l) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ln.1 3))
      (by linarith only [lp])
  have scaled : 0≤l*(1+l)*
      (r*(2-2*r+r*(1-(457/500)*r)/l)-2*l*(l+r-1)) := by
    rw [identity]
    exact add_nonneg first second
  have gap := nonneg_of_mul_nonneg_right scaled
    (mul_pos lp (by linarith only [lp] : 0<1+l))
  nlinarith only [gap,weighted]

#print axioms diagonal_minimum
#print axioms margin
end N12Compact.PositiveCentralCrossMargin
