import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Negative-L support margins for the actual negative-B endgame.
The C upper-face disjunction is retained. Two continuous slope ranges are
used only to bound a single coefficient; no sampled orientations occur. -/
namespace N12Compact.C849NegativeLeftScalar

theorem frame_bounds (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) :
    707/1000 ≤ c ∧ c ≤ 1 ∧ t ≤ 71/100 ∧ c*t ≤ 1/2 ∧
      1-c ≤ (293/500)*t^2 := by
  have squares := mul_nonneg (sub_nonneg.mpr order) (show 0 ≤ c+t by linarith)
  have cmin : 707/1000 ≤ c := by
    nlinarith only [unit,squares,hc,sq_nonneg (c-707/1000)]
  have cmax : c ≤ 1 := by nlinarith only [unit,sq_nonneg t,hc]
  have tmax : t ≤ 71/100 := by
    nlinarith only [unit,squares,ht,sq_nonneg (t-71/100)]
  have mixed : c*t ≤ 1/2 := by nlinarith only [unit,sq_nonneg (c-t)]
  have margin := mul_nonneg (sub_nonneg.mpr cmax)
    (show 0 ≤ (293/500)*(1+c)-1 by linarith only [cmin])
  exact ⟨cmin,cmax,tmax,mixed,by nlinarith only [margin,unit]⟩

private theorem coefficient_two (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) :
    2+(13/50)*t^2+(1/2)*c*t-c-t ≤ 1 := by
  obtain ⟨cmin,cmax,tmax,mixed,gap⟩ := frame_bounds c t hc ht order unit
  have product := mul_nonneg ht (sub_nonneg.mpr tmax)
  have linearGap : 1-c ≤ (3/7)*t := by nlinarith only [gap,product,ht]
  have projection : (13/50)*t+(1/2)*c ≤ 4/7 := by
    nlinarith only [unit,sq_nonneg ((1/2)*t-(13/50)*c),
      sq_nonneg ((13/50)*t+(1/2)*c-4/7),ht,hc]
  have product' := mul_nonneg ht (sub_nonneg.mpr projection)
  nlinarith only [linearGap,product']

private theorem coefficient_zero (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) (shallow : t ≤ (3/5)*c) :
    2-c-(7/20)*t^2-(3/20)*c*t ≤ 1 := by
  have squares := mul_nonneg (sub_nonneg.mpr shallow)
    (show 0 ≤ (3/5)*c+t by linarith)
  have cmin : 4/5 ≤ c := by
    nlinarith only [unit,squares,hc,sq_nonneg (c-4/5)]
  have cmax : c ≤ 1 := by nlinarith only [unit,sq_nonneg t,hc]
  have margin := mul_nonneg (sub_nonneg.mpr cmax)
    (show 0 ≤ (5/9)*(1+c)-1 by linarith only [cmin])
  have gap : 1-c ≤ (5/9)*t^2 := by nlinarith only [margin,unit]
  have slope := mul_nonneg ht (sub_nonneg.mpr shallow)
  have mixed := mul_nonneg hc.le ht
  nlinarith only [gap,slope,mixed]

private theorem coefficient_one (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (order : t ≤ c) (unit : c^2+t^2=1) (steep : (3/5)*c ≤ t) :
    113/50-c-(61/100)*t^2-(13/20)*c*t ≤ 1 := by
  obtain ⟨cmin,cmax,tmax,mixed,gap⟩ := frame_bounds c t hc ht order unit
  have difference := mul_nonneg
    (show 0 ≤ 2/5-c+t by linarith only [steep,cmax])
    (show 0 ≤ 2/5+c-t by linarith only [order])
  have mixedLower : 21/50 ≤ c*t := by nlinarith only [unit,difference]
  nlinarith only [gap,mixedLower,sq_nonneg t]

private theorem nonnegative_relative_margin (c t C u A Q : ℝ)
    (hc : 0 < c) (ht : 0 ≤ t) (order : t ≤ c) (unit : c^2+t^2=1)
    (hC : 0 < C) (hu : 0 ≤ u) (uC : u ≤ C) (unitL : C^2+u^2=1)
    (relative : 0 ≤ t*C-c*u) (hA : A ≤ 1) (hQ : Q ≤ -t) :
    A*C^2+Q*C*u+(457/500)*u^2-C ≤ 0 := by
  have cb := frame_bounds c t hc ht order unit
  have lb := frame_bounds C u hC hu uC unitL
  have aBound := mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg C)
  have qBound := mul_nonneg (show 0 ≤ -t-Q by linarith only [hQ])
    (mul_nonneg hC.le hu)
  have angle := mul_nonneg hu relative
  have square := mul_nonneg (show 0 ≤ c-1/2 by linarith only [cb.1]) (sq_nonneg u)
  nlinarith only [aBound,qBound,angle,square,lb.2.2.2.2,unitL]

private theorem negative_relative_margin (c t C u : ℝ)
    (hc : 0 < c) (ht : 0 ≤ t) (order : t ≤ c) (unit : c^2+t^2=1)
    (hC : 0 < C) (hu : 0 ≤ u) (uC : u ≤ C) (unitL : C^2+u^2=1)
    (relative : t*C-c*u ≤ 0) :
    C^2*(2-c)+(457/500)*u^2-C-(1/2+t)*C*u+
      (293/500)*c*C*(t*C-c*u) ≤ 0 := by
  have cb := frame_bounds c t hc ht order unit
  have lb := frame_bounds C u hC hu uC unitL
  have baseProduct := mul_nonneg hu (sub_nonneg.mpr uC)
  have base : C^2+(457/500)*u^2-C-(1/2)*C*u ≤ 0 := by
    nlinarith only [lb.2.2.2.2,baseProduct,unitL]
  have angle := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht hC.le) relative
  have multipliedUnit := congrArg (fun z : ℝ => C^2*z) unit
  dsimp only at multipliedUnit
  have squareGap := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr cb.2.1)
  have lifted : c*(C^2*(1-c)-t*C*u) ≤ 0 := by
    nlinarith only [angle,squareGap,multipliedUnit]
  have gap : C^2*(1-c)-t*C*u ≤ 0 := by
    exact nonpos_of_mul_nonpos_right lifted hc
  have last := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 293/500) hc.le) hC.le) relative
  nlinarith only [base,gap,last]

/-- Actual negative-L wall support and the original B point/cap data
contradict the sole remaining longitudinal separator. -/
theorem impossible (a c t C u U V W : ℝ)
    (ha : 1 < a) (hc : 0 < c) (ht : 0 ≤ t) (order : t ≤ c)
    (unit : c^2+t^2=1) (hC : 0 < C) (hu : 0 ≤ u) (uC : u ≤ C)
    (unitL : C^2+u^2=1)
    (wall : a*C-(457/500)*u^2-2*C*u ≤ C*W)
    (aCap : U+a ≤ 2*c-(5/2)*t)
    (bottom : V ≤ (33/20)*t+(47/20)*c)
    (high : 2*t+(1543/500)*c ≤ V+a)
    (cFace : U+a ≤ (113/50)*c-3*t ∨ V+a ≤ (113/50)*t+3*c)
    (axis : W ≤ (c*C+t*u)*U+(t*C-c*u)*(V+a/2)-a/2*|t*C-c*u|) : False := by
  have g : 0 < c*C+t*u := by positivity
  have cb := frame_bounds c t hc ht order unit
  have strict := mul_pos (sub_pos.mpr ha)
    (show 0 < C*(1+c*C+t*u) by positivity)
  have scaled := mul_le_mul_of_nonneg_left axis hC.le
  have aScaled := mul_le_mul_of_nonneg_left aCap (mul_nonneg hC.le g.le)
  have cuUnit := congrArg (fun z : ℝ => C^2*z) unit
  have suUnit := congrArg (fun z : ℝ => C*u*z) unit
  dsimp only at cuUnit suUnit
  by_cases sign : 0 ≤ t*C-c*u
  · rw [abs_of_nonneg sign] at scaled
    rcases cFace with cU | cV
    · have bottomScaled := mul_le_mul_of_nonneg_left bottom (mul_nonneg hC.le sign)
      by_cases shallow : t ≤ (3/5)*c
      · have coefficient := coefficient_zero c t hc ht order unit shallow
        have q : -(1/2)+(7/20)*c*t+(3/20)*c^2-t ≤ -t := by
          nlinarith only [cb.2.2.2.1,unit,sq_nonneg t]
        have margin := nonnegative_relative_margin c t C u _ _ hc ht order unit
          hC hu uC unitL sign coefficient q
        nlinarith only [scaled,aScaled,bottomScaled,wall,strict,margin,cuUnit,suUnit]
      · have coefficient := coefficient_one c t hc ht order unit (le_of_not_ge shallow)
        have q : -1+(61/100)*c*t+(13/20)*c^2-t ≤ -t := by
          nlinarith only [cb.2.2.2.1,unit,sq_nonneg t]
        have margin := nonnegative_relative_margin c t C u _ _ hc ht order unit
          hC hu uC unitL sign coefficient q
        have cScaled := mul_le_mul_of_nonneg_left cU (mul_nonneg hC.le g.le)
        nlinarith only [scaled,cScaled,bottomScaled,wall,strict,margin,cuUnit,suUnit]
    · have coefficient := coefficient_two c t hc ht order unit
      have q : -(1/2)-(13/50)*c*t-(1/2)*c^2-t+c ≤ -t := by
        nlinarith only [sq_nonneg (1-c),mul_nonneg hc.le ht]
      have margin := nonnegative_relative_margin c t C u _ _ hc ht order unit
        hC hu uC unitL sign coefficient q
      have cScaled := mul_le_mul_of_nonneg_left cV (mul_nonneg hC.le sign)
      have strict' := mul_pos (sub_pos.mpr ha)
        (show 0 < C*(1+c*C+t*u+(t*C-c*u)) by positivity)
      nlinarith only [scaled,aScaled,cScaled,wall,strict',margin,cuUnit,suUnit]
  · have sign' := le_of_not_ge sign
    rw [abs_of_nonpos sign'] at scaled
    have highScaled := mul_le_mul_of_nonpos_left high
      (mul_nonpos_of_nonneg_of_nonpos hC.le sign')
    have margin := negative_relative_margin c t C u hc ht order unit hC hu uC unitL sign'
    nlinarith only [scaled,aScaled,highScaled,wall,strict,margin,cuUnit,suUnit]

#print axioms impossible
end N12Compact.C849NegativeLeftScalar
