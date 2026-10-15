import Compact.Geometry.C977CornerSectorBounds

/-! Continuous scalar lemmas for the actual short-wall two-wall theorem.
These are the exact inequalities (1),(3),(6),(9),(10),(11),(15),(16)
of retained/walls/03. The wall endpoint remains 1197/500 throughout. -/
namespace N12Compact.C1092ShortWallScalars
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

noncomputable def allowance (c s : ℝ) : ℝ := (1-c)*(c+s-1)/2

theorem narrow_bounds {c s : ℝ} (cn : Normal c s) (narrow : 4*s ≤ c) :
    24/25 ≤ c ∧ s ≤ 1/4 ∧ 1-c ≤ (25/49)*s^2 := by
  classical
  have cb := normal_bounds cn
  have range := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0 ≤ c+4*s by linarith only [cb.1,cn.1])
  have low : 24/25 ≤ c := by
    by_contra bad
    have positive := mul_pos (sub_pos.mpr (lt_of_not_ge bad))
      (show 0 < c+24/25 by linarith only [cb.1])
    nlinarith only [positive,range,cn.2.2]
  have deficit := mul_nonneg (sub_nonneg.mpr low)
    (sub_nonneg.mpr cb.2.1)
  exact ⟨low,by linarith only [narrow,cb.2.1],
    by nlinarith only [deficit,cn.2.2]⟩

theorem allowance_bounds {c s : ℝ} (cn : Normal c s) (narrow : 4*s ≤ c) :
    0 ≤ allowance c s ∧ allowance c s ≤ s/50 ∧ allowance c s ≤ 1/200 := by
  have cb := normal_bounds cn
  have nb := narrow_bounds cn narrow
  have first := mul_nonneg (sub_nonneg.mpr cb.2.1)
    (show 0 ≤ c+s-1 by linarith only [cb.2.2.2.2.1])
  have upper := mul_le_mul
    (show 1-c ≤ (1/25 : ℝ) by linarith only [nb.1])
    (show c+s-1 ≤ s by linarith only [cb.2.1])
    (show 0 ≤ c+s-1 by linarith only [cb.2.2.2.2.1])
    (by norm_num : (0 : ℝ) ≤ 1/25)
  dsimp [allowance]
  exact ⟨by linarith only [first],by linarith only [upper],
    by linarith only [upper,nb.2.1]⟩

theorem cubic_baseline {c s : ℝ} (cn : Normal c s) (narrow : 4*s ≤ c) :
    (2/5)*s^3 ≤ s^2/2-(1-c)*(1-s)-s*allowance c s := by
  have cb := normal_bounds cn
  have nb := narrow_bounds cn narrow
  have interval := mul_nonneg cn.1 (sub_nonneg.mpr nb.2.1)
  have bracket : (8/5)*s ≤ s*(3-c-s)-(1-c) := by
    have monotone := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
    nlinarith only [monotone,nb.2.2,interval]
  have first := mul_nonneg (sub_nonneg.mpr cb.2.1) (sub_nonneg.mpr bracket)
  have second := mul_nonneg cn.1 (sq_nonneg (1-c))
  have identity : s^2/2-(1-c)*(1-s)-s*allowance c s =
      (1-c)*(s*(3-c-s)-(1-c))/2 := by
    unfold allowance
    linear_combination cn.2.2/2
  have radial : s*(1-c)^2 = 2*s*(1-c)-s^3 := by
    linear_combination s*cn.2.2
  nlinarith only [identity,first,second,radial]

theorem negative_wall_baseline {c s : ℝ} (cn : Normal c s) (narrow : 4*s ≤ c) :
    9/100 ≤ c-s-303/500+s^2+c*s/2-c*allowance c s := by
  have cb := normal_bounds cn
  have nb := narrow_bounds cn narrow
  have ab := allowance_bounds cn narrow
  have cap := mul_le_mul_of_nonneg_right cb.2.1 ab.1
  have product := mul_nonneg (show 0 ≤ c by linarith only [cb.1]) cn.1
  nlinarith only [nb.1,nb.2.1,ab.2.2,cap,product,sq_nonneg s]

theorem central_positive_below {c s r t : ℝ}
    (cn : Normal c s) (rn : Normal r t) (narrow : 4*s ≤ c) (order : t ≤ s) :
    0 ≤ r*(1+c*r+s*t-2*c)-(457/500)*s*t := by
  have cb := normal_bounds cn
  have rb := normal_bounds rn
  have nb := narrow_bounds cn narrow
  have cosine := cosine_order cn rn order
  have term0 := mul_nonneg (show 0 ≤ r by linarith only [rb.1])
    (sub_nonneg.mpr cosine)
  have term1 := mul_nonneg
    (mul_nonneg (show 0 ≤ r by linarith only [rb.1]) (sub_nonneg.mpr cb.2.1))
    (sub_nonneg.mpr rb.2.1)
  have term2 := mul_nonneg (mul_nonneg cn.1 rn.1)
    (show 0 ≤ r-457/500 by linarith only [cosine,nb.1])
  have identity : r*(1+c*r+s*t-2*c)-(457/500)*s*t =
      r*(r-c)+r*(1-c)*(1-r)+s*t*(r-457/500) := by ring
  nlinarith only [identity,term0,term1,term2]

theorem central_negative_below {c s r t : ℝ}
    (cn : Normal c s) (rn : Normal r t) (narrow : 4*s ≤ c) :
    0 ≤ r+(c*r-s*t)*(r+t)-2*c*r+(457/500)*s*t := by
  have cb := normal_bounds cn
  have rb := normal_bounds rn
  have cp : 0 ≤ c := by linarith only [cb.1]
  have rp : 0 < r := by linarith only [rb.1]
  have chordProduct := mul_nonneg rn.1
    (show 0 ≤ 1+r-2*t by linarith only [rn.2.1,rb.2.2.2.1])
  have chordIdentity : (1+r)*(2*r+t-2) = t*(1+r-2*t) := by
    linear_combination 2*rn.2.2
  have chord : t/2 ≤ r+t-1 := by
    have nonneg : 0 ≤ (1+r)*(2*r+t-2) := by
      linarith only [chordProduct,chordIdentity]
    have difference := nonneg_of_mul_nonneg_right nonneg (by linarith only [rp])
    linarith only [difference]
  have first := mul_nonneg rp.le (sub_nonneg.mpr cb.2.1)
  have second := mul_nonneg (mul_nonneg cp rp.le) (sub_nonneg.mpr chord)
  have third := mul_nonneg (mul_nonneg cn.1 rn.1)
    (show 0 ≤ 3/5-(r+t-457/500) by linarith only [rb.2.2.2.2.2])
  have fourth := mul_nonneg rn.1 (sub_nonneg.mpr narrow)
  have last := mul_nonneg (mul_nonneg cp rn.1)
    (show 0 ≤ r/2-3/20 by linarith only [rb.1])
  have identity : r+(c*r-s*t)*(r+t)-2*c*r+(457/500)*s*t =
      r*(1-c)+c*r*(r+t-1)-s*t*(r+t-457/500) := by ring
  nlinarith only [first,second,third,fourth,last,identity]

/-- The steep sector uses the actual short-wall convex-combination point
and has a rational nonnegative quadratic certificate. -/
theorem steep_short_point {c s : ℝ} (cn : Normal c s) (steep : 16*c/25 ≤ s) :
    ((1293/1250)*c+(591/2500)*s)^2 ≤ 1 := by
  have cb := normal_bounds cn
  have term0 := mul_nonneg (sub_nonneg.mpr steep)
    (show 0 ≤ s+3*c/25 by linarith only [cn.1,cb.1])
  have term1 := sq_nonneg c
  have term2 := mul_nonneg (show 0 ≤ c by linarith only [cb.1]) cn.1
  have term3 := sq_nonneg s
  have identity : 1-((1293/1250)*c+(591/2500)*s)^2 =
      (471/500)*(s-16*c/25)*(s+3*c/25)+
        (3691/1562500)*c^2+(303/390625)*c*s+(13219/6250000)*s^2 := by
    linear_combination -cn.2.2
  nlinarith only [identity,term0,term1,term2,term3]

/-- The moderate sector retains the endpoint 197/500 exactly. -/
theorem moderate_short_point {c s : ℝ} (cn : Normal c s) (moderate : c ≤ 4*s) :
    303/500 ≤ (197/500)*c+s := by
  have cb := normal_bounds cn
  have positive : 0 ≤ (197/500)*c+s := by linarith only [cb.1,cn.1]
  have term0 := mul_nonneg (sub_nonneg.mpr moderate)
    (show 0 ≤ 4*s+6*c by linarith only [cb.1,cn.1])
  have term1 := mul_nonneg (show 0 ≤ c by linarith only [cb.1]) cn.1
  have term2 := sq_nonneg s
  have identity : ((197/500)*c+s)^2-(303/500)^2 =
      (53/1500)*(4*s-c)*(4*s+6*c)+(61/750)*c*s+(50573/750000)*s^2 := by
    linear_combination (91809/250000)*cn.2.2
  nlinarith only [identity,positive,term0,term1,term2]

#print axioms cubic_baseline
#print axioms steep_short_point
#print axioms moderate_short_point
end N12Compact.C1092ShortWallScalars
