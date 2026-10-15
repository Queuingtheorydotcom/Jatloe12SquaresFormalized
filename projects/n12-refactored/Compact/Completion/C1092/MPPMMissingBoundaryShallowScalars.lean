import Compact.Geometry.C977CornerCubic
import Compact.Completion.CommonCases.CanonicalScalars

/-! Exact scalar comparisons in C1092-MPPM-MISSING-BOUNDARY-SHALLOW-ANGLE,
sections 4--6. The final monotonicity comparison is replaced by the weaker
rational consequence b+r>6/5 at r/b>=1/4. The whole canonical intervals,
including equal normals, remain in every statement. Source-only. -/
namespace N12Compact.C1092MPPMMissingBoundaryShallow
open C977CornerCubic
set_option Elab.async false
noncomputable section

def crossCos (c s b r : ℝ) : ℝ := c*b-s*r
def crossSin (c s b r : ℝ) : ℝ := c*r+s*b

theorem strict_bounds {c s : ℝ} (cn : Normal c s) (sp : 0<s) :
    7/10<c ∧ c<1 ∧ s<177/250 ∧ 1<c+s ∧ c+s≤99/70 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have base := CommonCases.CanonicalScalars.bounds c s cp cn.1 cn.2.1 cn.2.2
  have cu : c<1 := by nlinarith only [cn.2.2,sq_pos_of_pos sp,cp]
  have squareOrder := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (add_nonneg cp.le cn.1)
  have su : s<177/250 := by
    by_contra no
    have square := mul_nonneg (show 0≤s-177/250 by linarith only [no])
      (show 0≤s+177/250 by linarith only [sp])
    nlinarith only [cn.2.2,squareOrder,square]
  have sumLow : 1<c+s := by
    have product := mul_pos cp sp
    nlinarith only [cn.2.2,product,base.2.2.1]
  have sumHigh : c+s≤99/70 := by
    by_contra no
    have square := mul_pos (show 0<c+s-99/70 by linarith only [no])
      (show 0<c+s+99/70 by linarith only [sumLow])
    nlinarith only [cn.2.2,sq_nonneg (c-s),square]
  exact ⟨base.1,cu,su,sumLow,sumHigh⟩

theorem cross_bounds {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (sp : 0<s) (rp : 0<r) :
    0≤crossCos c s b r ∧ 0<crossSin c s b r ∧
      crossCos c s b r≤b ∧ r≤crossSin c s b r := by
  have cb := strict_bounds cn sp
  have bb := strict_bounds bn rp
  have cp : 0<c := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have first := mul_nonneg (sub_nonneg.mpr cn.2.1) bp.le
  have last := mul_nonneg cn.1 (sub_nonneg.mpr bn.2.1)
  have high := mul_nonneg bp.le (sub_nonneg.mpr cb.2.1.le)
  have product := mul_nonneg cn.1 bn.1
  have sum := mul_nonneg bn.1 (sub_nonneg.mpr cb.2.2.2.1.le)
  dsimp only [crossCos,crossSin]
  refine ⟨by nlinarith only [first,last],by positivity,
    by nlinarith only [high,product],by nlinarith only [sum,last]⟩

private theorem sum_gap {b r : ℝ} (bn : Normal b r) (rp : 0<r) :
    (207/250)*b*r<b+r-1 := by
  have bb := strict_bounds bn rp
  have bp : 0<b := by linarith only [bb.1]
  have coefficient : 0<2-(207/250)*(1+b+r) := by
    linarith only [bb.2.2.2.2]
  have product := mul_pos (mul_pos bp rp) coefficient
  have identity : (1+b+r)*(b+r-1-(207/250)*b*r)=
      b*r*(2-(207/250)*(1+b+r)) := by
    linear_combination bn.2.2
  rw [←identity] at product
  have margin := (mul_pos_iff_of_pos_left
    (show 0<1+b+r by linarith only [bp,rp])).mp product
  linarith only [margin]

/-- Section 4, after decreasing the actual common side to one. -/
theorem northwest_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (sp : 0<s) (rp : 0<r) :
    0<b+r-2+b^2+r*(crossCos c s b r*(1-c-s/2)+
      crossSin c s b r*(1-s)) := by
  have cb := strict_bounds cn sp
  have bb := strict_bounds bn rp
  have cp : 0<c := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have crossed := cross_bounds cn bn sp rp
  have chord : c+s/2<1119/1000 := by
    by_contra no
    have product := mul_nonneg (show 0≤c+s/2-1119/1000 by linarith only [no])
      (show 0≤c+s/2+1119/1000 by linarith only [cp,sp])
    nlinarith only [product,cn.2.2,sq_nonneg (c-2*s)]
  have kWeight := mul_nonneg crossed.1
    (show 0≤1-c-s/2+119/1000 by linarith only [chord])
  have kBound := mul_nonneg (by norm_num : (0:ℝ)≤119/1000)
    (sub_nonneg.mpr crossed.2.2.1)
  have ellWeight := mul_pos crossed.2.1
    (show 0<1-s-73/250 by linarith only [cb.2.2.1])
  have ellBound := mul_nonneg (by norm_num : (0:ℝ)≤73/250)
    (sub_nonneg.mpr crossed.2.2.2)
  have insideMargin : -(119/1000)*b+(73/250)*r<
      crossCos c s b r*(1-c-s/2)+crossSin c s b r*(1-s) := by
    nlinarith only [kWeight,kBound,ellWeight,ellBound]
  have weighted := mul_lt_mul_of_pos_left insideMargin rp
  have sum := sum_gap bn rp
  have remaining := mul_nonneg bn.1 (sub_nonneg.mpr bn.2.1)
  have strict := mul_pos bp rp
  nlinarith only [weighted,sum,remaining,strict,bn.2.2]

/-- Section 5. Direct comparison with the two unit normals replaces
the equivalent P0,Q0 Cauchy--Schwarz calculation. -/
theorem central_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (sp : 0<s) (rp : 0<r) :
    0<crossSin c s b r*(b+r)+r-2*crossSin c s b r+s*(b-r) := by
  have cb := strict_bounds cn sp
  have bb := strict_bounds bn rp
  have cp : 0<c := by linarith only [cb.1]
  have bp : 0<b := by linarith only [bb.1]
  have coefficient : 0<1+b-2*r := by linarith only [bn.2.1,bb.2.1]
  have product := mul_pos rp coefficient
  have identity : (1+b)*(2*b+r-2)=r*(1+b-2*r) := by
    linear_combination 2*bn.2.2
  rw [←identity] at product
  have first : 0<2*b+r-2 :=
    (mul_pos_iff_of_pos_left (show 0<1+b by linarith only [bp])).mp product
  have second : 0<r^2-(1-b)*(b+r) := by
    have term := mul_pos (sub_pos.mpr bb.2.1)
      (show 0<1-r by linarith only [bb.2.2.1])
    nlinarith only [term,bn.2.2]
  have dot : 0≤1-c*b-s*r := by
    nlinarith only [cn.2.2,bn.2.2,sq_nonneg (c-b),sq_nonneg (s-r)]
  have strict := mul_pos (mul_pos rp cp) first
  have last := mul_nonneg cn.1 second.le
  have floor := mul_nonneg bn.1 dot
  have expansion :
      crossSin c s b r*(b+r)+r-2*crossSin c s b r+s*(b-r)=
      r*(1-c*b-s*r)+r*c*(2*b+r-2)+s*(r^2-(1-b)*(b+r)) := by
    dsimp only [crossSin]
    ring
  nlinarith only [expansion,strict,last,floor]

/-- The two canonical C-angle floors from section 6, with rational
constants. Their proofs retain the diagonal endpoint. -/
theorem angle_floors {c s : ℝ} (cn : Normal c s) (sp : 0<s) :
    457/500<c+s-c*s ∧ 1/2≤c-s+s^2 := by
  have cb := strict_bounds cn sp
  have first := mul_nonneg (sub_nonneg.mpr cb.2.2.2.2)
    (show 0≤99/70+(c+s)-2 by linarith only [cb.2.2.2.1])
  have second := mul_nonneg (sub_nonneg.mpr cn.2.1)
    (show 0≤2-(c+s) by linarith only [cb.2.2.2.2])
  constructor <;> nlinarith only [first,second,cn.2.2]

/-- The manuscript's scalar (19) is positive whenever r/b>=1/4.
Its exact unit-circle relation gives b+r>6/5, which already suffices. -/
private theorem boundary_margin {b r : ℝ} (bn : Normal b r) (rp : 0<r)
    (large : b≤4*r) : 0<b+r-543/500+(43/250)*r^2-b*r/2 := by
  have bb := strict_bounds bn rp
  have bp : 0<b := by linarith only [bb.1]
  have order := mul_nonneg (sub_nonneg.mpr large)
    (show 0≤4*b-r by linarith only [bn.2.1,bp])
  have cross : 4/17≤b*r := by nlinarith only [order,bn.2.2]
  have sum : 6/5<b+r := by
    by_contra no
    have square := mul_nonneg (show 0≤6/5-(b+r) by linarith only [no])
      (show 0≤6/5+(b+r) by linarith only [bp,rp])
    nlinarith only [square,cross,bn.2.2]
  have quadratic := mul_nonneg (sub_nonneg.mpr sum.le)
    (show 0≤7/10-(b+r)/4 by linarith only [bb.2.2.2.2])
  nlinarith only [quadratic,bn.2.2,sq_nonneg r]

/-- Section 6's strict opposite-to-separation scalar, on the entire
excluded range r/b>=1/4. No point sample or angle subdivision occurs. -/
theorem northeast_margin {c s b r : ℝ} (cn : Normal c s) (bn : Normal b r)
    (sp : 0<s) (rp : 0<r) (large : b≤4*r) :
    0<b+r-2-b*r+(543/500)*r^2+
      b^2*(c+s-c*s)+b*r*(c-s+s^2) := by
  have floors := angle_floors cn sp
  have bb := strict_bounds bn rp
  have bp : 0<b := by linarith only [bb.1]
  have first := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr floors.1.le)
  have second := mul_nonneg (mul_nonneg bp.le bn.1) (sub_nonneg.mpr floors.2)
  have base := boundary_margin bn rp large
  nlinarith only [first,second,base,bn.2.2]

end
end N12Compact.C1092MPPMMissingBoundaryShallow
