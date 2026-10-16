import Compact.Completion.C1092.TwoFifthsData

/-! Northeast half-angle interval and the two continuous physical-wall
width comparisons. Exact finite differences on the unit circle replace
all monotonicity derivatives in sections 5--6 of the supplied proof. -/
namespace N12Compact.C1092TwoFifths.Scalars
open S12 S12Pilot C977CornerCubic
set_option Elab.async false
noncomputable section

structure NorthBounds (b t : ℝ) : Prop where
  cosineLow : 4/5≤b
  cosineHigh : b<15/17
  sineLow : 8/17<t
  sineHigh : t≤3/5
  ratioLow : 8*b<15*t
  ratioHigh : 4*t≤3*b
  coefficient : 11/10<b+t-(3/5)*b*t
  remainder : -(23/125)≤b-t-3/5+(3/5)*t^2
  upperArc : t+b/2≤1

theorem north_bounds (b t : ℝ) (normal : Normal b t) (bp : 0<b) (tp : 0<t)
    (halfLow : 1+b<4*t) (halfHigh : 3*t≤1+b) : NorthBounds b t := by
  have first := mul_nonneg (show 0≤1+b-3*t by linarith only [halfHigh])
    (show 0≤1+b+3*t by linarith only [bp,tp])
  have bLow : 4/5≤b := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<4/5-b by linarith only [bad])
      (show 0<1+b by linarith only [bp])
    nlinarith only [first,product,normal.2.2]
  have tHigh : t≤3/5 := by
    apply le_of_not_gt
    intro bad
    have product := mul_pos (show 0<t-3/5 by linarith only [bad])
      (show 0<t+3/5 by linarith only [tp])
    have cosine := mul_nonneg (sub_nonneg.mpr bLow)
      (show 0≤b+4/5 by linarith only [bp])
    nlinarith only [product,cosine,normal.2.2]
  have second := mul_pos (show 0<4*t-1-b by linarith only [halfLow])
    (show 0<4*t+1+b by linarith only [bp,tp])
  have bHigh : b<15/17 := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤b-15/17 by linarith only [bad])
      (show 0≤b+1 by linarith only [bp])
    nlinarith only [second,product,normal.2.2]
  have tLow : 8/17<t := by
    apply lt_of_not_ge
    intro bad
    have product := mul_nonneg (show 0≤8/17-t by linarith only [bad])
      (show 0≤8/17+t by linarith only [tp])
    have cosine := mul_pos (sub_pos.mpr bHigh)
      (show 0<15/17+b by linarith only [bp])
    nlinarith only [product,cosine,normal.2.2]
  have sumLow : 23/17<b+t := by
    have product := mul_pos (sub_pos.mpr tLow)
      (show 0<b-t+7/17 by linarith only [normal.2.1])
    have identity : (b+t-23/17)*(b+15/17)=(t-8/17)*(b-t+7/17) := by
      nlinarith only [normal.2.2]
    have positive : 0<(b+t-23/17)*(b+15/17) := by rwa [identity]
    exact sub_pos.mp (pos_of_mul_pos_left positive (by linarith only [bp]))
  have sumHigh := (normal_bounds normal).2.2.2.2.2
  have difference := mul_pos (sub_pos.mpr sumLow)
    (show 0<1-(3/10)*(b+t+23/17) by linarith only [sumHigh])
  have coefficient : 11/10<b+t-(3/5)*b*t := by
    nlinarith only [difference,normal.2.2]
  have last := mul_nonneg (show 0≤3/5-t by linarith only [tHigh])
    (show 0≤1-(3/5)*(t+3/5) by linarith only [tHigh])
  have remainder : -(23/125)≤b-t-3/5+(3/5)*t^2 := by
    nlinarith only [last,bLow]
  have arcProduct := mul_nonneg (show 0≤3/5-t by linarith only [tHigh])
    (show 0≤b+4/5-(t+3/5)/2 by linarith only [bLow,tHigh])
  have arcIdentity : (1-t-b/2)*(b+4/5)=
      (3/5-t)*(b+4/5-(t+3/5)/2) := by
    nlinarith only [normal.2.2]
  have upperArc : t+b/2≤1 := by
    have product : 0≤(1-t-b/2)*(b+4/5) := by rwa [arcIdentity]
    have gap := nonneg_of_mul_nonneg_left product (show 0<b+4/5 by linarith only [bp])
    linarith only [gap]
  exact ⟨bLow,bHigh,tLow,tHigh,by linarith only [bHigh,tLow],
    by linarith only [bLow,tHigh],coefficient,remainder,upperArc⟩

theorem small_right (d r : ℝ) (normal : Normal d r) (small : r≤(2/5)*d) :
    r≤2/5 ∧ r≤(1+d)/5 ∧ 0≤d+r/5-1 := by
  have b := normal_bounds normal
  have ru : r≤2/5 := by linarith only [small,b.2.1]
  have half : r≤(1+d)/5 := by linarith only [small,b.2.1]
  have product := mul_nonneg normal.1 (sub_nonneg.mpr half)
  have identity : (1+d)*(d+r/5-1)=r*((1+d)/5-r) := by
    nlinarith only [normal.2.2]
  have gap : 0≤(1+d)*(d+r/5-1) := by rwa [identity]
  exact ⟨ru,half,nonneg_of_mul_nonneg_right gap (by linarith only [b.1])⟩

/-- The width in the negative right frame dominates its value at the
aligned endpoint, including equality r=0. -/
theorem negative_width (b t d r : ℝ) (north : Normal b t)
    (right : Normal d r) (small : r≤(2/5)*d) :
    2*t+b≤(2*t+b)*d+b*r := by
  have bounds := normal_bounds north
  have rb := normal_bounds right
  have half := (small_right d r right small).2.1
  have first := mul_le_mul_of_nonneg_left half
    (show 0≤2*t+b by linarith only [north.1,bounds.1])
  have second := mul_nonneg (show 0≤1+d by linarith only [rb.1])
    (show 0≤b-(2*t+b)/5 by linarith only [north.1,north.2.1,bounds.1])
  have bracket : 0≤b*(1+d)-(2*t+b)*r := by nlinarith only [first,second]
  have product := mul_nonneg right.1 bracket
  have identity : (1+d)*((2*t+b)*d+b*r-(2*t+b))=
      r*(b*(1+d)-(2*t+b)*r) := by
    linear_combination (2*t+b)*right.2.2
  have gap : 0≤(1+d)*((2*t+b)*d+b*r-(2*t+b)) := by rwa [identity]
  have bound := nonneg_of_mul_nonneg_right gap (show 0<1+d by linarith only [rb.1])
  linarith only [bound]

/-- Same actual wall, positive right frame. The finite circle difference
compares the whole north interval directly to b=4/5,t=3/5. -/
theorem positive_width (b t d r : ℝ) (north : Normal b t) (h : NorthBounds b t)
    (right : Normal d r) (small : r≤(2/5)*d) :
    0≤1-b-2*t+((2*t+b)*d+(2*t-b)*r)/2 := by
  let P := 1-d/2+r/2
  let Q := 2-d-r
  have rb := normal_bounds right
  have sr := small_right d r right small
  have pn : 0≤P := by dsimp [P]; linarith only [rb.2.1,right.1]
  have comparison : 0≤Q-(3/4)*P := by
    dsimp [P,Q]
    linarith only [rb.2.1,sr.1]
  have first := mul_nonneg pn
    (show 0≤(3/4)*(b+4/5)-(t+3/5) by linarith only [h.cosineLow,h.sineHigh])
  have second := mul_nonneg comparison
    (show 0≤b+4/5 by linarith only [h.cosineLow])
  have bracket : 0≤Q*(b+4/5)-P*(t+3/5) := by nlinarith only [first,second]
  have product := mul_nonneg (show 0≤3/5-t by linarith only [h.sineHigh]) bracket
  have identity : ((1-b*P-t*Q)-(d+r/5-1))*(b+4/5)=
      (3/5-t)*(Q*(b+4/5)-P*(t+3/5)) := by
    dsimp [P,Q]
    linear_combination -(1-d/2+r/2)*north.2.2
  have difference : 0≤((1-b*P-t*Q)-(d+r/5-1))*(b+4/5) := by rwa [identity]
  have bound := nonneg_of_mul_nonneg_left difference
    (show 0<b+4/5 by linarith only [h.cosineLow])
  dsimp [P,Q] at bound
  nlinarith only [bound,sr.2.2]

end
#print axioms north_bounds
#print axioms negative_width
#print axioms positive_width
end N12Compact.C1092TwoFifths.Scalars
