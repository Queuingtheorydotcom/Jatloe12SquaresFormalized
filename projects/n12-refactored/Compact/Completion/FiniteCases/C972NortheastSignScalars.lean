import Compact.Geometry.C977CornerCubic

noncomputable section

/-! Two exact full-angle margins for the genuine southeast/northeast
comparison in C972. The normals retain their closed canonical endpoints. -/
namespace N12Compact.FiniteCases.C972Local.NortheastScalars
open C977CornerCubic
set_option Elab.async false

theorem north_transverse {c s d r : ℝ} (source : Normal c s)
    (north : Normal d r) (cosine : 4/5<c) (sine : s<1/2) :
    0<d*(c-61/100-(6/25)*c^2)+r*(13/20-s+(6/25)*c*s) := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have dp : 0<d := by linarith only [db.1]
  have coefficient : 0<1-(6/25)*(c+4/5) := by linarith only [cb.2.1]
  have factor := mul_nonneg (show 0≤c-4/5 by linarith only [cosine]) coefficient.le
  have first : 0<c-61/100-(6/25)*c^2 := by nlinarith only [factor]
  have cross := mul_nonneg (show 0≤c by linarith only [cb.1]) source.1
  have last : 0<13/20-s+(6/25)*c*s := by nlinarith only [sine,cross]
  exact add_pos_of_pos_of_nonneg (mul_pos dp first) (mul_nonneg north.1 last.le)

def A (d r : ℝ) : ℝ := 17/20-r+(92/125)*r^2+(7/20)*d*r
def B (d r : ℝ) : ℝ := 1-d-(7/20)*r^2+(92/125)*d*r

theorem source_transverse {c s d r : ℝ} (source : Normal c s)
    (north : Normal d r) : 0<1-c*A d r-s*B d r := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have cp : 0<c := by linarith only [cb.1]
  have dn : 0≤d := by linarith only [db.1]
  have sine : r≤5/7 := by linarith only [north.2.1,db.2.2.2.2.2]
  have coefficient : (92/125)*r+(7/20)*d≤1 := by
    linarith only [sine,db.2.1]
  have weight := mul_nonneg north.1 (sub_nonneg.mpr coefficient)
  have capA : A d r≤17/20 := by dsimp only [A]; nlinarith only [weight]
  have defect := mul_nonneg
    (show 0≤1-d by linarith only [db.2.1])
    (show 0≤d-7/10 by linarith only [db.1])
  have chord : 1-d≤(10/17)*r^2 := by nlinarith only [defect,north.2.2]
  have ordered := mul_nonneg (sub_nonneg.mpr north.2.1) (add_nonneg dn north.1)
  have square : r^2≤1/2 := by nlinarith only [ordered,north.2.2]
  have cross : d*r≤1/2 := by nlinarith only [sq_nonneg (d-r),north.2.2]
  have capB : B d r<1/2 := by dsimp only [B]; linarith only [chord,square,cross]
  have short : (17/20)*c+(1/2)*s<1 := by
    nlinarith only [source.2.2,sq_nonneg ((1/2)*c-(17/20)*s),
      sq_nonneg ((17/20)*c+(1/2)*s-1)]
  have first := mul_nonneg cp.le (sub_nonneg.mpr capA)
  have last := mul_nonneg source.1 (sub_nonneg.mpr capB.le)
  nlinarith only [first,last,short]

#print axioms north_transverse
#print axioms source_transverse
end N12Compact.FiniteCases.C972Local.NortheastScalars
