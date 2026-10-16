import Compact.Geometry.C977CornerCubic
import Mathlib.Tactic.LinearCombination

/-! Complete canonical-arc margins for the MMMP northeast sign theorem.
Weighted sums and exact products replace the paper's derivative estimates. -/
namespace N12Compact.C1092MMMPNortheastSignScalars
open C977CornerCubic
set_option Elab.async false

theorem longitudinal {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t) :
    b*(27/20-d-r+(13/20)*d*r-(37/50)*r^2)+
      t*(2+r-d-(37/50)*d*r-(13/20)*r^2)<1 := by
  have db := normal_bounds dn
  have bb := normal_bounds bn
  let F := 27/20-d-r+(13/20)*d*r-(37/50)*r^2
  let G := 2+r-d-(37/50)*d*r-(13/20)*r^2
  have dr := mul_nonneg (show 0≤d by linarith only [db.1]) dn.1
  have first := mul_nonneg (show 0≤1-d by linarith only [db.2.1])
    (show 0≤(6/5)*(1+d)-2 by linarith only [db.1])
  have tail := mul_nonneg dn.1 (show 0≤1-d by linarith only [db.2.1])
  have sum : F+G≤27/20 := by
    dsimp [F,G]
    nlinarith only [first,dn.2.2,dr,sq_nonneg r]
  have order : F≤G := by
    dsimp [F,G]
    nlinarith only [tail,dn.1,sq_nonneg r]
  have difference := mul_nonneg (sub_nonneg.mpr bn.2.1) (sub_nonneg.mpr order)
  have weighted := mul_nonneg
    (show 0≤b+t by linarith only [bb.1,bn.1]) (sub_nonneg.mpr sum)
  dsimp [F,G] at difference weighted
  nlinarith only [difference,weighted,bb.2.2.2.2.2]

private theorem coefficient_bounds {b t : ℝ} (bn : Normal b t)
    (steep : 9/20<t) (narrow : b<9/10) :
    19/200<b+t-1-(61/100)*b*t ∧ b+t-1-(61/100)*b*t<1 ∧
      49/200<1-b+t-(61/100)*t^2 ∧ 1-b+t-(61/100)*t^2≤139/200 := by
  have bb := normal_bounds bn
  have bp : 0≤b := by linarith only [bb.1]
  have low : 67/50<b+t := by
    apply lt_of_not_ge
    intro bad
    have first := mul_pos (show 0<t-9/20 by linarith only [steep])
      (show 0<b-9/20 by linarith only [steep,bn.2.1])
    have last := mul_nonneg (show 0≤67/50-(b+t) by linarith only [bad])
      (show 0≤67/50+b+t-9/10 by linarith only [bp,bn.1])
    nlinarith only [first,last,bn.2.2]
  have sumhigh := bb.2.2.2.2.2
  have chord := mul_pos (show 0<b+t-67/50 by linarith only [low])
    (show 0<1-(61/200)*(b+t+67/50) by linarith only [sumhigh])
  have bt := mul_nonneg bp bn.1
  have rsmall := mul_nonneg (sub_nonneg.mpr bn.2.1) (add_nonneg bp bn.1)
  have tcap : t^2≤1/2 := by nlinarith only [rsmall,bn.2.2]
  have curve := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤1-(61/200)*(b+t) by linarith only [sumhigh])
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [chord,bn.2.2]
  · linarith only [sumhigh,bt]
  · nlinarith only [narrow,steep,tcap]
  · nlinarith only [curve,bn.2.2]

private theorem short_projection {d r A B : ℝ} (unit : d^2+r^2=1)
    (an : 0<A) (au : A<181/200) (bl : -61/200≤B) (bu : B≤61/200) :
    d*A+r*B<1 := by
  have first := mul_pos
    (show 0<181/200-A by linarith only [au])
    (show 0<181/200+A by linarith only [an])
  have last := mul_nonneg
    (show 0≤61/200-B by linarith only [bu])
    (show 0≤61/200+B by linarith only [bl])
  have norm : (d*A+r*B)^2+(r*A-d*B)^2=A^2+B^2 := by
    linear_combination (A^2+B^2)*unit
  nlinarith only [first,last,norm,sq_nonneg (r*A-d*B),sq_nonneg (d*A+r*B-1)]

theorem transverse {d r b t : ℝ} (dn : Normal d r) (bn : Normal b t)
    (steep : 9/20<t) (narrow : b<9/10) :
    -d*(b+t-1-(61/100)*b*t)+r*(1-b+t-(61/100)*t^2)<1+(39/100)*r-d := by
  obtain ⟨klow,khigh,jlow,jhigh⟩ := coefficient_bounds bn steep narrow
  have result := short_projection dn.2.2
    (show 0<1-(b+t-1-(61/100)*b*t) by linarith only [khigh])
    (show 1-(b+t-1-(61/100)*b*t)<181/200 by linarith only [klow])
    (show -61/200≤(1-b+t-(61/100)*t^2)-39/100 by linarith only [jlow])
    (show (1-b+t-(61/100)*t^2)-39/100≤61/200 by linarith only [jhigh])
  linarith only [result]

#print axioms longitudinal
#print axioms transverse
end N12Compact.C1092MMMPNortheastSignScalars
