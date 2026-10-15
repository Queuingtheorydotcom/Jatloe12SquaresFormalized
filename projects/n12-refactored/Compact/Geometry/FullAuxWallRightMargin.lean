import Compact.Geometry.C977CornerSectorBounds
import Mathlib.Tactic.LinearCombination

/-! A quadratic support margin for the full positive right-wall square.
The proof uses a single continuous interval and exact rational bounds;
there is no angle subdivision or numerical premise. -/
namespace N12Compact.FullAuxWallRightMargin
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

theorem central_bounds {c s : ℝ} (an : Normal c s) (narrow : 4*s≤c) :
    24/25≤c ∧ s≤1/4 ∧ 1-c≤(25/49)*s^2 ∧
      -(3/25)*s^2≤(2/5)*s^2-(1-c)*(1-s) ∧
      11/100≤c-s-3/5+s^2+(2/5)*c*s := by
  have ab := normal_bounds an
  have cp : 0≤c := by linarith only [ab.1]
  have small : s≤1/4 := by linarith only [narrow,ab.2.1]
  have sSquare := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/4+s by linarith only [an.1])
  have wide : 24/25≤c := by
    apply le_of_not_gt
    intro no
    have square := mul_pos (sub_pos.mpr no)
      (show 0<24/25+c by linarith only [cp])
    nlinarith only [square,sSquare,an.2.2]
  have defect : 1-c≤(25/49)*s^2 := by
    have product := mul_nonneg (sub_nonneg.mpr ab.2.1)
      (sub_nonneg.mpr wide)
    nlinarith only [product,an.2.2]
  have baseline : -(3/25)*s^2≤(2/5)*s^2-(1-c)*(1-s) := by
    have product := mul_nonneg an.1 (sub_nonneg.mpr ab.2.1)
    nlinarith only [product,defect,sq_nonneg s]
  refine ⟨wide,small,defect,baseline,?_⟩
  have product := mul_nonneg cp an.1
  nlinarith only [wide,small,product,sq_nonneg s]

/-- In the nonnegative right-wall sector, the central square's own
separator is excluded by three elementary nonnegative products. -/
theorem positive_u_margin {c s r t : ℝ} (an : Normal c s) (rn : Normal r t)
    (narrow : 4*s≤c) (ordered : t≤s) :
    0≤r*(1+c*r+s*t-2*c)-(457/500)*s*t := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have bounds := central_bounds an narrow
  have orderC := cosine_order an rn ordered
  have rp : 0≤r := by linarith only [rb.1]
  have first := mul_nonneg rp (sub_nonneg.mpr orderC)
  have second := mul_nonneg
    (mul_nonneg rp (sub_nonneg.mpr ab.2.1)) (sub_nonneg.mpr rb.2.1)
  have third := mul_nonneg (mul_nonneg an.1 rn.1)
    (show 0≤r-457/500 by linarith only [bounds.1,orderC])
  have identity : r*(1+c*r+s*t-2*c)-(457/500)*s*t=
      r*(r-c)+r*(1-c)*(1-r)+s*t*(r-457/500) := by ring
  linarith only [identity,first,second,third]

/-- The same central-square separator is impossible throughout the
negative right-wall sector, with no order restriction on its angle. -/
theorem negative_u_margin {c s r t : ℝ} (an : Normal c s) (rn : Normal r t)
    (narrow : 4*s≤c) :
    0≤r+(c*r-s*t)*(r+t)-2*c*r+(457/500)*s*t := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have cp : 0≤c := by linarith only [ab.1]
  have rp : 0<r := by linarith only [rb.1]
  have reach : t/2≤r+t-1 := by
    have product := mul_nonneg rn.1
      (show 0≤1+r-2*t by linarith only [rn.2.1,rb.2.2.2.1])
    have identity : (1+r)*(2*r+t-2)=t*(1+r-2*t) := by
      linear_combination 2*rn.2.2
    have nonnegative : 0≤(1+r)*(2*r+t-2) := by
      linarith only [identity,product]
    have result := nonneg_of_mul_nonneg_right nonnegative
      (show 0<1+r by linarith only [rp])
    linarith only [result]
  have first := mul_nonneg rp.le (sub_nonneg.mpr ab.2.1)
  have main := mul_nonneg (mul_nonneg cp rp.le) (sub_nonneg.mpr reach)
  have cap := mul_nonneg (mul_nonneg an.1 rn.1)
    (show 0≤3/5-(r+t-457/500) by linarith only [rb.2.2.2.2.2])
  have slope := mul_nonneg rn.1
    (show 0≤c/4-s by linarith only [narrow])
  have gap := mul_nonneg (mul_nonneg cp rn.1)
    (show 0≤r/2-3/20 by linarith only [rb.1])
  have identity : r+(c*r-s*t)*(r+t)-2*c*r+(457/500)*s*t=
      r*(1-c)+c*r*(r+t-1)-s*t*(r+t-457/500) := by ring
  nlinarith only [identity,first,main,cap,slope,gap]

/-- Across the whole shallow right-wall arc, the support margin is
bounded below by its axis-aligned endpoint. -/
theorem baseline_margin {c s r t : ℝ} (an : Normal c s) (rn : Normal r t)
    (narrow : 4*s≤c) (ordered : t≤s) :
    (2/5)*s^2-(1-c)*(1-s)≤
      r^2*(2+(2/5)*s^2-c*s)+r*t*(1-s^2-(2/5)*c*s)+
      r*((c*r+s*t)-(c*t-s*r)+1)+(1543/500)*t^2-4 := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have cp : 0≤c := by linarith only [ab.1]
  have bounds := central_bounds an narrow
  have small : s≤1/4 := bounds.2.1
  have sSquare := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤1/4+s by linarith only [an.1])
  have wide : 24/25≤c := bounds.1
  have orderC : c≤r := cosine_order an rn ordered
  have rWide : 24/25≤r := le_trans wide orderC
  have rDefect : 1-r≤(25/49)*t^2 := by
    have product := mul_nonneg (sub_nonneg.mpr rb.2.1)
      (sub_nonneg.mpr rWide)
    nlinarith only [product,rn.2.2]
  let A := 2+c+s+(2/5)*s^2-c*s
  let B := 1-c+s-s^2-(2/5)*c*s
  let M := r^2*A+r*t*B+r+(1543/500)*t^2-4
  let M0 := (2/5)*s^2-(1-c)*(1-s)
  have cap : A≤121/40 := by
    have product := mul_nonneg (sub_nonneg.mpr ab.2.1)
      (show 0≤1-s by linarith only [small])
    dsimp [A]
    nlinarith only [product,sSquare]
  have bLower : (19/40)*s≤B := by
    have product := mul_nonneg an.1 (sub_nonneg.mpr ab.2.1)
    have smallProduct := mul_nonneg an.1 (sub_nonneg.mpr small)
    have identity : B-((3/5)*s-(1/2)*s^2)=
        (1/2)*(1-c)^2+(2/5)*s*(1-c) := by
      dsimp [B]
      linear_combination (-1/2)*an.2.2
    nlinarith only [identity,product,smallProduct,sq_nonneg (1-c)]
  have bp : 0≤B := by linarith only [bLower,an.1]
  have rB : (57/125)*s≤r*B := by
    have product := mul_nonneg (sub_nonneg.mpr rWide) bp
    nlinarith only [product,bLower]
  have weightedB := mul_nonneg rn.1 (sub_nonneg.mpr rB)
  have quadratic := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr cap)
  have mixed := mul_nonneg rn.1 (sub_nonneg.mpr ordered)
  have difference : M-M0=r*t*B+((1543/500)-A)*t^2-(1-r) := by
    dsimp [M,M0,A]
    linear_combination A*rn.2.2
  have monotone : M0≤M := by
    nlinarith only [difference,weightedB,quadratic,rDefect,mixed,sq_nonneg t]
  dsimp [M0,M,A,B] at monotone
  convert monotone using 1 <;> ring

/-- The surviving right-square U separator controls the central square's
excess over its center face by a quantity quadratic in its sine. -/
theorem margin {c s r t : ℝ} (an : Normal c s) (rn : Normal r t)
    (narrow : 4*s≤c) (ordered : t≤s) :
    0≤r^2*(2+(2/5)*s^2-c*s)+r*t*(1-s^2-(2/5)*c*s)+
      r*((c*r+s*t)-(c*t-s*r)+1)+(1543/500)*t^2-4+
      (1/5)*r*(c*r+s*t)*s^2 := by
  have bounds := central_bounds an narrow
  have monotone := baseline_margin an rn narrow ordered
  have baseline := bounds.2.2.2.1
  have rp : 0≤r := by linarith only [(normal_bounds rn).1]
  have tSmall : t≤1/4 := le_trans ordered bounds.2.1
  have tSquare := mul_nonneg (sub_nonneg.mpr tSmall)
    (show 0≤1/4+t by linarith only [rn.1])
  have projection : 9/10≤r*(c*r+s*t) := by
    have first := mul_nonneg (sub_nonneg.mpr bounds.1) (sq_nonneg r)
    have second := mul_nonneg (mul_nonneg rp an.1) rn.1
    nlinarith only [first,second,tSquare,rn.2.2]
  have weighted := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr projection)
  nlinarith only [monotone,baseline,weighted,sq_nonneg s]

#print axioms baseline_margin
#print axioms margin
#print axioms positive_u_margin
#print axioms negative_u_margin
end N12Compact.FullAuxWallRightMargin
