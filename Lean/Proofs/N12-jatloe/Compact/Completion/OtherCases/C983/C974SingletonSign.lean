import Compact.Completion.OtherCases.C983.C974MissingCornerSupports

/-! MISSING-CORNER-WALL-SIGN Theorem 2: once the adjacent actual W
has its positive canonical frame, the nonpositive canonical frame of K
is impossible. The endpoint sigma=0 and diagonal K are retained.
Source translation only; this is not a compiler acceptance claim. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- The elementary common bound x(1-h)≤l/4, with the exact half-angle
relation kept explicit. Used in WALL-SIGN §3.4 and MIDPOINT §1.4. -/
theorem quarter_defect (l h x : ℝ) (lp : 0<l) (hp : 0<h)
    (unit : l^2+h^2=1) (relation : x*(1+l)=h) : x*(1-h)≤l/4 := by
  have lu : l≤1 := by nlinarith only [unit,sq_nonneg h,lp]
  have hu : h≤1 := by nlinarith only [unit,sq_nonneg l,hp]
  have denominator : 0<(1+h)*(1+l) := by positivity
  have first := mul_nonneg (sub_nonneg.mpr hu) (show 0≤1+l by positivity)
  have last := mul_nonneg (show 0≤2*h by positivity) (sub_nonneg.mpr lu)
  have product : 4*h*l≤(1+h)*(1+l) := by nlinarith only [first,last]
  have identity : x*(1-h)*((1+h)*(1+l))=h*l^2 := by
    calc
      _ = (x*(1+l))*(1-h)*(1+h) := by ring
      _ = h*(1-h)*(1+h) := by rw [relation]
      _ = h*l^2 := by nlinarith only [show h*(l^2+h^2-1)=0 by rw [unit]; ring]
  have weighted := mul_nonneg lp.le (sub_nonneg.mpr product)
  apply (mul_le_mul_iff_left₀ denominator).mp
  rw [identity]
  nlinarith only [weighted]

/-- The two strict continuous estimates of WALL-SIGN §§3.3--3.4. -/
theorem noncanonical_scalars (l h d t x : ℝ)
    (lp : 0<l) (hp : 0<h) (orderK : l≤h) (ku : l^2+h^2=1)
    (dp : 0<d) (tn : 0≤t) (orderW : t≤d) (wu : d^2+t^2=1)
    (relation : x*(1+l)=h) :
    0≤1-d+(1-h)*(d*x-t) ∧
      0<(l*d+h*t)*(1-d)+(h*d-l*t)*(1-d/2)-x*(1-h) := by
  have hu : h<1 := by nlinarith only [ku,sq_pos_of_pos lp,hp]
  have du : d≤1 := by nlinarith only [wu,sq_nonneg t,dp]
  have hl : 7/10<h := by
    have compare := mul_nonneg (sub_nonneg.mpr orderK) (show 0≤h+l by positivity)
    nlinarith only [compare,ku,hp]
  have dl : 7/10<d := by
    have compare := mul_nonneg (sub_nonneg.mpr orderW) (show 0≤d+t by positivity)
    nlinarith only [compare,wu,dp]
  have xl : 2/5<x := by
    apply (mul_lt_mul_iff_left₀ (show 0<1+l by positivity)).mp
    rw [relation]
    linarith only [orderK,hl]
  have smallProjection : (22/25)*d+(3/10)*t<1 := by
    nlinarith only [wu,sq_nonneg ((3/10)*d-(22/25)*t)]
  have first : 0≤1-d+(1-h)*(d*x-t) := by
    by_cases sign : 0≤d*x-t
    · have positive := mul_nonneg (show 0≤1-h by linarith only [hu]) sign
      linarith only [du,positive]
    · have sign' : d*x-t<0 := lt_of_not_ge sign
      have height := mul_pos (show 0<h-7/10 by linarith only [hl]) (neg_pos.mpr sign')
      have half := mul_pos dp (show 0<x-2/5 by linarith only [xl])
      nlinarith only [height,half,smallProjection]
  let A := d*(1-d/2)+t*(1-d)
  let B := d*(4-3*d-t)/2
  have Ap : 0<A := by
    have first := mul_pos dp (show 0<1-d/2 by linarith only [du])
    have last := mul_nonneg tn (show 0≤1-d by linarith only [du])
    dsimp only [A]
    linarith only [first,last]
  have projection : 3*d+t<13/4 := by
    nlinarith only [wu,sq_nonneg (d-3*t)]
  have Bp : 21/80<B := by
    have first := mul_pos dp (show 0<13/4-(3*d+t) by linarith only [projection])
    dsimp only [B]
    nlinarith only [first,dl]
  have identity : (l*d+h*t)*(1-d)+(h*d-l*t)*(1-d/2)=(h-l)*A+l*B := by
    dsimp only [A,B]
    ring
  have leading := mul_nonneg (sub_nonneg.mpr orderK) Ap.le
  have last := mul_pos lp (show 0<B-21/80 by linarith only [Bp])
  have defect := quarter_defect l h x lp hp ku relation
  refine ⟨first,?_⟩
  rw [identity]
  nlinarith only [leading,last,defect,lp]

/-- The reindexed quadrant frame of a nonpositive canonical singleton
has c≤s. Its two remaining supports contradict the scalar comparisons. -/
theorem steep_quadrant_impossible (K W : OpenSquare) (e : Input K W)
    (lp : 0<K.c) (hp : 0<K.s) (orderK : K.c≤K.s)
    (dp : 0<W.c) (tn : 0≤W.s) (orderW : W.s≤W.c)
    (cap : K.loV+K.side≤0) : False := by
  have relative : 0≤K.s*W.c-K.c*W.s := by
    have first := mul_nonneg (sub_nonneg.mpr orderK) dp.le
    have last := mul_nonneg lp.le (sub_nonneg.mpr orderW)
    nlinarith only [first,last]
  have obstruction := positive_support_obstruction K W e lp hp dp tn orderW cap relative
  have scalars := noncanonical_scalars K.c K.s W.c W.s (K.s/(1+K.c))
    lp hp orderK K.unit_normal dp tn orderW W.unit_normal
    (div_mul_cancel₀ _ (by positivity : (1+K.c:ℝ)≠0))
  rcases obstruction with first | last
  · exact (not_lt_of_ge scalars.1) first
  · exact (not_lt_of_ge scalars.2.le) last

theorem singleton_canonical_positive (K W : OpenSquare) (e : Input K W)
    (cp : 0<K.c) (canonical : |K.s|≤K.c)
    (dp : 0<W.c) (tn : 0≤W.s) (orderW : W.s≤W.c) : 0<K.s := by
  by_contra no
  have sign := singleton_negative_cap K W e cp (le_of_not_gt no)
  have framed := e.reframeK (R:=turnFrame K) rfl (by intro x y; exact turnFrame_inside K x y)
  apply steep_quadrant_impossible (turnFrame K) W framed
  · change 0< -K.s
    linarith only [sign.1]
  · exact cp
  · change -K.s≤K.c
    linarith only [(abs_le.mp canonical).1]
  · exact dp
  · exact tn
  · exact orderW
  · change -K.loU-K.side+K.side≤0
    linarith only [sign.2]

end
#print axioms singleton_canonical_positive
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
