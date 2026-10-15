import Compact.Completion.CommonCases.UnitCircleChord
import Compact.Completion.OtherCases.SharpPointScalars

/-! Exact margins for the two remaining actual transverse axes in C972.
Every comparison is a unit-circle identity, a rational chord, or a sum
of nonnegative products. The two relative-angle orders retain equality. -/
namespace N12Compact.FiniteCases.C972Local.NortheastPositiveScalars
open C977CornerCubic
set_option Elab.async false

theorem relative_order {c s d r : ℝ} (source : Normal c s) (north : Normal d r)
    (order : c*r≤s*d) : r≤s ∧ c≤d := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have cp : 0<c := by linarith only [cb.1]
  have dn : 0≤d := by linarith only [db.1]
  have sine : r≤s := by
    apply le_of_not_gt
    intro large
    have cosine := CommonCases.UnitCircleChord.cosine_order cp.le dn
      source.2.2 north.2.2 source.1 north.1 large.le
    have first := mul_pos cp (sub_pos.mpr large)
    have last := mul_nonneg source.1 (sub_nonneg.mpr cosine)
    nlinarith only [first,last,order]
  exact ⟨sine,CommonCases.UnitCircleChord.cosine_order dn cp.le
    north.2.2 source.2.2 north.1 source.1 sine⟩

theorem alpha_lower {c s d r : ℝ} (source : Normal c s) (north : Normal d r)
    (order : s≤r) : d≤c*d+s*r := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have first := mul_nonneg
    (show 0≤1-d by linarith only [db.2.1])
    (show 0≤1-c by linarith only [cb.2.1])
  have last := mul_nonneg source.1 (sub_nonneg.mpr order)
  have defect := mul_nonneg
    (show 0≤c by linarith only [cb.1])
    (show 0≤1-c by linarith only [cb.2.1])
  nlinarith only [first,last,defect,source.2.2]

theorem right_projection {d r : ℝ} (north : Normal d r) :
    (293/500)*d+d*r<1 := by
  have upper : d≤1-r^2/2 := by nlinarith only [north.2.2,sq_nonneg (d-1)]
  nlinarith only [upper,north.2.2,sq_nonneg (d-(5/4)*r),sq_nonneg r]

def P (c s : ℝ) : ℝ := 673/500-c+(6/25)*c^2
def Q (c s : ℝ) : ℝ := 1-s+(6/25)*c*s

theorem north_axis_shallower {c s d r : ℝ} (source : Normal c s) (north : Normal d r)
    (cosine : 4/5<c) (sine : s<1/2) (order : r≤s) :
    0<1-d*P c s-r*Q c s := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have cp : 0<c := by linarith only [cosine]
  have dn : 0≤d := by linarith only [db.1]
  have first : 0≤P c s := by dsimp only [P]; nlinarith only [cb.2.1,sq_nonneg c]
  have cross := mul_nonneg cp.le source.1
  have last : 0≤Q c s := by dsimp only [Q]; nlinarith only [sine,cross]
  have derivative : 0≤Q c s*c-P c s*s := by
    dsimp only [P,Q]
    nlinarith only [cosine,sine]
  have chord := CommonCases.UnitCircleChord.increasing
    (c:=c) (s:=s) (d:=d) (t:=r) (A:=P c s) (B:=Q c s)
    cp dn source.2.2 north.2.2 source.1 north.1 order first last derivative
  have identity : P c s*c+Q c s*s=(793/500)*c+s-1 := by
    dsimp only [P,Q]
    linear_combination ((6/25)*c-1)*source.2.2
  have short : (793/500)*c+s<2 := by
    nlinarith only [source.2.2,sq_nonneg (c-(793/500)*s),
      sq_nonneg ((793/500)*c+s-2)]
  nlinarith only [chord,identity,short]

def Aplus (d r : ℝ) : ℝ := 793/500-d-(92/125)*r^2+(7/20)*d*r
def Bplus (d r : ℝ) : ℝ := 13/20-r+(7/20)*r^2+(92/125)*d*r

theorem source_axis_steeper {c s d r : ℝ} (source : Normal c s) (north : Normal d r) :
    0<1-c*Aplus d r-s*Bplus d r := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have cp : 0<c := by linarith only [cb.1]
  have sine : r≤5/7 := by linarith only [north.2.1,db.2.2.2.2.2]
  have defect := mul_nonneg
    (show 0≤1-d by linarith only [db.2.1])
    (show 0≤d-2/3 by linarith only [db.1])
  have chord : 1-d≤(3/5)*r^2 := by nlinarith only [defect,north.2.2]
  have capA : Aplus d r≤18/25 := by
    dsimp only [Aplus]
    nlinarith only [chord,north.2.2,sq_nonneg (d-(7/5)*r),sq_nonneg d,sq_nonneg r]
  have coefficient : (7/20)*r+(92/125)*d≤1 := by
    linarith only [sine,db.2.1]
  have weight := mul_nonneg north.1 (sub_nonneg.mpr coefficient)
  have capB : Bplus d r≤13/20 := by dsimp only [Bplus]; nlinarith only [weight]
  have short : (18/25)*c+(13/20)*s<1 := by
    nlinarith only [source.2.2,sq_nonneg ((13/20)*c-(18/25)*s),
      sq_nonneg ((18/25)*c+(13/20)*s-1)]
  have first := mul_nonneg cp.le (sub_nonneg.mpr capA)
  have last := mul_nonneg source.1 (sub_nonneg.mpr capB)
  nlinarith only [first,last,short]

def Aminus (d r : ℝ) : ℝ := 793/500-d+r-(413/500)*r^2
def Bminus (d r : ℝ) : ℝ := 1-d-r+(413/500)*d*r

theorem source_axis_shallower {c s d r : ℝ} (source : Normal c s) (north : Normal d r)
    (positive : 0<r) (order : c≤d) :
    0<1-c*Aminus d r-s*Bminus d r := by
  have cb := normal_bounds source
  have db := normal_bounds north
  have dp : 0<d := by linarith only [db.1]
  have sine : r≤5/7 := by linarith only [north.2.1,db.2.2.2.2.2]
  have product := mul_nonneg north.1
    (show 0≤1-(413/500)*r by linarith only [sine])
  have coefficient : 0≤Aminus d r := by dsimp only [Aminus]; nlinarith only [product,db.2.1]
  have arc := Completion.OtherCases.SharpPointScalars.arc d r dp positive north.2.2
  have capB : Bminus d r≤0 := by dsimp only [Bminus]; linarith only [arc]
  have upper : d≤1-r^2/2 := by nlinarith only [north.2.2,sq_nonneg (d-1)]
  have weight := mul_nonneg (sq_nonneg r)
    (show 0≤d-7/10 by linarith only [db.1])
  have capA : d*Aminus d r<1 := by
    dsimp only [Aminus]
    nlinarith only [upper,weight,north.2.2,sq_nonneg (d-(5/4)*r),sq_nonneg r]
  have first := mul_nonneg (sub_nonneg.mpr order) coefficient
  have last := mul_nonpos_of_nonneg_of_nonpos source.1 capB
  nlinarith only [first,last,capA]

#print axioms north_axis_shallower
#print axioms source_axis_steeper
#print axioms source_axis_shallower
end N12Compact.FiniteCases.C972Local.NortheastPositiveScalars
