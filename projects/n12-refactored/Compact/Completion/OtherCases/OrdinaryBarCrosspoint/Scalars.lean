import Compact.Completion.CommonCases.CanonicalScalars

/-! The two arctan(1/2) projection comparisons of ORDINARY-BAR-CROSSPOINT
section 2, proved by factored quadratic differences. This avoids sqrt,
trigonometric and derivative dependencies while keeping the full intervals. -/
namespace N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Scalars
set_option Elab.async false

theorem before_half (c t : ℝ) (cp : 0<c) (tn : 0≤t)
    (unit : c^2+t^2=1) (angle : 2*t≤c) : (293/500)*c+t<1 := by
  have coefficient : 0≤(750151/250000)*c+(17651/125000)*t := by
    linarith only [cp,tn]
  have margin := mul_nonneg (show 0≤c-2*t by linarith only [angle]) coefficient
  have identity : (2172/1000)^2-5*((293/500)*c+t)^2=
      (c-2*t)*((750151/250000)*c+(17651/125000)*t) := by
    linear_combination -(294849/62500 : ℝ)*unit
  nlinarith only [identity,margin,sq_nonneg ((293/500)*c+t-1)]

theorem after_half (c t : ℝ) (cp : 0<c) (tn : 0≤t)
    (unit : c^2+t^2=1) (angle : c≤2*t) : c+(103/500)*t<1 := by
  have coefficient : 0≤(33391/250000)*c+(290891/125000)*t := by
    linarith only [cp,tn]
  have margin := mul_nonneg (show 0≤2*t-c by linarith only [angle]) coefficient
  have identity : (2206/1000)^2-5*(c+(103/500)*t)^2=
      (2*t-c)*((33391/250000)*c+(290891/125000)*t) := by
    linear_combination -(1216609/250000 : ℝ)*unit
  nlinarith only [identity,margin,sq_nonneg (c+(103/500)*t-1)]

theorem lower_vertex (c t : ℝ) (cp : 0<c) (tn : 0≤t) (order : t≤c)
    (unit : c^2+t^2=1) : 1≤c+(1/2)*c*t+(13/50)*t^2 := by
  have bounds := CommonCases.CanonicalScalars.bounds c t cp tn order unit
  have orderProduct := mul_nonneg tn (sub_nonneg.mpr order)
  have remainder := mul_nonneg (show 0≤1-c by linarith only [bounds.2.1])
    (show 0≤(19/25)*c-6/25 by linarith only [bounds.1])
  nlinarith only [unit,orderProduct,remainder]

end N12Compact.Completion.OtherCases.OrdinaryBarCrosspoint.Scalars
