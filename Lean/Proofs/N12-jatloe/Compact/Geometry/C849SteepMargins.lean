import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Uniform scalar margins for A/B in the transverse upper-left-marker
sector of 849/851. These are inequalities over complete real angle arcs,
not sampled orientations or numerical certificates. -/
namespace N12Compact.C849SteepMargins

structure Bounds (c s : ℝ) : Prop where
  cLow : 7/10 ≤ c
  cHigh : c ≤ 4/5
  sLow : 3/5 ≤ s
  sHigh : s ≤ 71/100
  order : s ≤ c
  sumLow : 7/5 ≤ c+s
  sumHigh : c+s ≤ 10/7
  difference : c-s ≤ 1/5

theorem bounds (c s a : ℝ) (hc : 0 < c) (hs : 0 ≤ s)
    (order : s ≤ c) (unit : c^2+s^2=1)
    (ha : 1<a) (height : a≤s+c/2) : Bounds c s := by
  have steep : 3*c/4<s := by
    apply lt_of_not_ge
    intro shallow
    have product := mul_nonneg hc.le (show 0≤3*c/4-s by linarith only [shallow])
    have above : 1<s+c/2 := lt_of_lt_of_le ha height
    nlinarith only [unit,product,above,sq_nonneg (s+c/2-1)]
  have slope := mul_nonneg (sub_nonneg.mpr order) (add_nonneg hc.le hs)
  have slope' := mul_pos (sub_pos.mpr steep)
    (show 0<s+3*c/4 by linarith only [hc,hs])
  have cLow : 7/10≤c := by nlinarith only [unit,slope,hc,sq_nonneg (c-7/10)]
  have cHigh : c≤4/5 := by nlinarith only [unit,slope',sq_nonneg (c-4/5)]
  have sLow : 3/5≤s := by nlinarith only [unit,cHigh,hc,hs,sq_nonneg (s-3/5)]
  have sHigh : s≤71/100 := by nlinarith only [unit,slope,hs,sq_nonneg (s-71/100)]
  have difference : c-s≤1/5 := by linarith only [cHigh,sLow]
  have diffSquare := mul_nonneg (show 0≤1/5-(c-s) by linarith only [difference])
    (show 0≤1/5+(c-s) by linarith only [order])
  have sumLow : 7/5≤c+s := by
    nlinarith only [unit,diffSquare,hc,hs,sq_nonneg (c+s-7/5)]
  have sumHigh : c+s≤10/7 := by
    nlinarith only [unit,sq_nonneg (c-s),sq_nonneg (c+s-10/7)]
  exact ⟨cLow,cHigh,sLow,sHigh,order,sumLow,sumHigh,difference⟩

private theorem frame (p q : ℝ) (hp : 0≤p) (hq : 0≤q) (unit : p^2+q^2=1) :
    p≤1 ∧ q≤1 ∧ 1≤p+q ∧ p+q≤10/7 ∧ p*q≤1/2 := by
  have product := mul_nonneg hp hq
  refine ⟨?_,?_,?_,?_,?_⟩
  · nlinarith only [unit,sq_nonneg q,sq_nonneg (p-1)]
  · nlinarith only [unit,sq_nonneg p,sq_nonneg (q-1)]
  · nlinarith only [unit,product,hp,hq,sq_nonneg (p+q-1)]
  · nlinarith only [unit,sq_nonneg (p-q),sq_nonneg (p+q-10/7)]
  · nlinarith only [unit,sq_nonneg (p-q)]

private theorem weighted (c s F G : ℝ) (hc : 0≤c) (hs : 0≤s)
    (order : s≤c) (sum : c+s≤10/7)
    (fg : F≤G) (total : F+G≤11/8) : c*F+s*G<1 := by
  have h₀ := mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr fg)
  have h₁ := mul_nonneg (add_nonneg hc hs) (sub_nonneg.mpr total)
  nlinarith only [h₀,h₁,sum]

/-- A's lower-V missing-marker mode, separation on B's axis,
when A's angle is at least B's angle. -/
theorem lowerV_b_pos (p q c s : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) (unitB : c^2+s^2=1)
    (hc : 0≤c) (hs : 0≤s) (order : q≤p) (cross : 0≤c*q-s*p) :
    0 < 1+(c*p+s*q)+(c*q-s*p)+(13/20)*(c*q-s*p)*(p-q)
      -(27/20)*(c*p+s*q)*(p+q) := by
  have f := frame p q hp hq unit
  have dot : 0≤c*p+s*q := add_nonneg (mul_nonneg hc hp) (mul_nonneg hs hq)
  have dotHigh : c*p+s*q≤1 := by
    nlinarith only [unit,unitB,sq_nonneg (p-c),sq_nonneg (q-s)]
  have product := mul_nonneg dot (show 0≤10/7-(p+q) by linarith only [f.2.2.2.1])
  have extra := mul_nonneg cross (sub_nonneg.mpr order)
  nlinarith only [product,extra,cross,dotHigh]

/-- The other sign of the relative angle uses A's compulsory P to
bound the negatively weighted lower longitudinal face. -/
theorem lowerV_b_neg (p q c s : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) (hc : 0≤c) (hs : 0≤s)
    (order : q≤p) (orderB : s≤c) (sumB : c+s≤10/7) :
    0 < 1+(c*p+s*q)+(c*q-s*p)*(p-(37/50)*q)
      -(27/20)*(c*p+s*q)*(p+q) := by
  have f := frame p q hp hq unit
  let F := (27/20)*p^2+(7/20)*p*q+(37/50)*q^2-p
  let G := p^2+(61/100)*p*q+(27/20)*q^2-q
  have sign := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤1-(7/20)*(p+q) by linarith only [f.2.2.2.1])
  have product := mul_nonneg hq (add_nonneg hp hq)
  have fg : F≤G := by dsimp [F,G]; nlinarith only [sign,product]
  have quadratic := mul_nonneg (show 0≤p+q-1 by linarith only [f.2.2.1])
    (show 0≤3/2-(p+q) by linarith only [f.2.2.2.1])
  have qBound := mul_nonneg hq (sub_nonneg.mpr f.1)
  have total : F+G≤11/8 := by
    dsimp [F,G]
    nlinarith only [unit,quadratic,qBound,sq_nonneg (13*q-4)]
  have small := weighted c s F G hc hs orderB sumB fg total
  dsimp [F,G] at small
  nlinarith only [small]

/-- A's lower-U mode imposes q≥3/7; the full interval remains continuous. -/
theorem lowerU_b_pos (p q c s : ℝ) (hp : 0≤p) (hq : 3/7≤q)
    (unit : p^2+q^2=1) (hc : 0≤c) (hs : 0≤s)
    (orderB : s≤c) (sumB : c+s≤10/7) :
    0 < 1+(c*p+s*q)+(c*q-s*p)+(27/20)*(c*q-s*p)*(p-q)
      -(c*p+s*q)*(2*q+(3/5)*p) := by
  have qNonneg : 0≤q := by linarith only [hq]
  have f := frame p q hp qNonneg unit
  let F := (3/5)*p^2+(13/20)*p*q+(27/20)*q^2-p-q
  let G := (27/20)*p^2-(3/4)*p*q+2*q^2+p-q
  have product := mul_nonneg hp (sub_nonneg.mpr f.2.1)
  have fg : F≤G := by
    dsimp [F,G]
    nlinarith only [product,hp,sq_nonneg p,sq_nonneg q]
  have interval := mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr f.2.1)
  have pq := mul_nonneg hp qNonneg
  have total : F+G≤11/8 := by dsimp [F,G]; nlinarith only [unit,interval,pq]
  have small := weighted c s F G hc hs orderB sumB fg total
  dsimp [F,G] at small
  nlinarith only [small]

/-- On A's axis and the positive relative-angle branch, a single short
vector provides the uniform margin. -/
theorem lowerV_a_pos (p q c s : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) (b : Bounds c s) (cross : 0≤c*q-s*p) :
    0 < 1+(c*p+s*q)-(27/20)*(p+q)+(c*q-s*p)*c := by
  have cp := mul_nonneg hp (sub_nonneg.mpr b.cLow)
  have sq := mul_nonneg hq (sub_nonneg.mpr b.sLow)
  have extra := mul_nonneg cross (show 0≤c by linarith only [b.cLow])
  have short : (13/20)*p+(3/4)*q<1 := by
    nlinarith only [unit,sq_nonneg ((3/4)*p-(13/20)*q),
      sq_nonneg ((13/20)*p+(3/4)*q-1)]
  nlinarith only [cp,sq,extra,short]

/-- On A's axis and the negative relative-angle branch, all B angles
are handled by two bounded scalar coefficients. -/
theorem lowerV_a_neg (p q c s : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) (b : Bounds c s) :
    0 < 1+(c*p+s*q)-(27/20)*(p+q)
      +(13/20)*(c*q-s*p)*(c-s) := by
  have f := frame p q hp hq unit
  have hnonneg : 0≤c-s := sub_nonneg.mpr b.order
  have h₀ := mul_nonneg hnonneg (sub_nonneg.mpr b.sHigh)
  have h₁ := mul_nonneg hnonneg (sub_nonneg.mpr b.cLow)
  have first : 27/20-c+(13/20)*s*(c-s)≤33/50 := by
    nlinarith only [b.sumLow,h₀,hnonneg]
  have second : 27/20-s-(13/20)*c*(c-s)≤33/50 := by
    nlinarith only [b.sumLow,b.difference,h₁]
  have weightedFirst := mul_le_mul_of_nonneg_left first hp
  have weightedSecond := mul_le_mul_of_nonneg_left second hq
  nlinarith only [weightedFirst,weightedSecond,f.2.2.2.1]

/-- The high-angle A sector uses the actual right neighbour at (3,2.4).
The upper marker of B may be weakened to height3 in this inequality. -/
theorem lowerU_a_pos (p q c s : ℝ) (hp : 0≤p) (hq : 0≤q)
    (unit : p^2+q^2=1) (unitB : c^2+s^2=1) (b : Bounds c s) :
    0 < 1+(c*p+s*q)-(2*q+(3/5)*p)+(c*q-s*p)*c := by
  have sBelow : 0≤1-s := by linarith only [b.sHigh]
  have product := mul_nonneg (sub_nonneg.mpr b.cLow) sBelow
  have first : 3/5-c+c*s≤2/5 := by nlinarith only [product,b.sHigh]
  have interval := mul_nonneg (sub_nonneg.mpr b.sLow) (sub_nonneg.mpr b.sHigh)
  have second : 1-s+s^2≤4/5 := by nlinarith only [interval,b.sHigh]
  have wp := mul_le_mul_of_nonneg_left first hp
  have wq := mul_le_mul_of_nonneg_left second hq
  have uq := congrArg (fun z : ℝ => q*z) unitB
  have short : (2/5)*p+(4/5)*q<1 := by
    nlinarith only [unit,sq_nonneg ((4/5)*p-(2/5)*q),
      sq_nonneg ((2/5)*p+(4/5)*q-1)]
  nlinarith only [wp,wq,uq,short]

end N12Compact.C849SteepMargins
