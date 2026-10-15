import Compact.Geometry.PositiveWallUpperVImpossible

/-! The actual central escape confines a negative bottom singleton to a
small continuous angle sector. The bound is a quadratic identity on the
whole canonical arc; no angle subdivision or numerical pose is used. -/
namespace N12Compact.PositiveCornerSmallBottom
open C977CornerCubic
set_option Elab.async false

theorem tilt {c t C S : ℝ} (on : Normal c t) (an : Normal C S)
    (escape : (C+S)*(1-(7/20)*C)<1)
    (separatedScalar : boundary c t <
      c*(2+C*S-C-S)+t*(2-S^2-C+S)) : t<1/5 := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cp : 0<c := by linarith only [ob.1]
  have Cp : 0<C := by linarith only [ab.1]
  have large := PositiveWallUpperVImpossible.cosine_bound an escape
  have cosineSquare := mul_nonneg (show 0≤C-81/100 by linarith only [large])
    (show 0≤C+81/100 by linarith only [Cp])
  have sine : S≤59/100 := by
    by_contra no
    have product := mul_pos (show 0<S-59/100 by linarith only [no])
      (show 0<S+59/100 by linarith only [an.1])
    nlinarith only [product,cosineSquare,an.2.2]
  have difference := mul_nonneg
    (show 0≤C-S-11/50 by linarith only [large,sine])
    (show 0≤C-S+11/50 by linarith only [an.2.1])
  have sum : C+S≤7/5 := by
    nlinarith only [difference,an.2.2,sq_nonneg (C+S-7/5)]
  have firstProduct := mul_nonneg (sub_nonneg.mpr sum)
    (show 0≤C+S-3/5 by linarith only [ab.2.2.2.2.1])
  have first : 2+C*S-C-S≤27/25 := by
    nlinarith only [firstProduct,an.2.2]
  have secondProduct := mul_nonneg (sub_nonneg.mpr an.2.1)
    (show 0≤1-(C+S)/2 by linarith only [sum])
  have second : 2-S^2-C+S≤3/2 := by
    nlinarith only [secondProduct,an.2.2]
  have cosine : c≤1-t^2/2 := by
    nlinarith only [on.2.2,sq_nonneg (c-1)]
  have arc := mul_nonneg (sub_nonneg.mpr on.2.1)
    (show 0≤c+t by linarith only [cp,on.1])
  have t_high : t≤3/4 := by
    by_contra no
    have product := mul_pos (show 0<t-3/4 by linarith only [no])
      (show 0<t+3/4 by linarith only [on.1])
    nlinarith only [product,arc,on.2.2]
  have boundary_product := mul_nonneg
    (mul_nonneg on.1 (sub_nonneg.mpr ob.2.2.2.1))
    (sub_nonneg.mpr ob.2.1)
  have boundary_identity :
      c*(boundary c t-(1+2*t-t^2))=t*(1-t)*(1-c) := by
    unfold boundary
    field_simp [cp.ne'] <;> ring
  have boundary_lower : 1+2*t-t^2≤boundary c t := by
    have scaled : 0≤c*(boundary c t-(1+2*t-t^2)) := by
      linarith only [boundary_identity,boundary_product]
    have gap := nonneg_of_mul_nonneg_right scaled cp
    linarith only [gap]
  have firstWeight := mul_nonneg cp.le (sub_nonneg.mpr first)
  have secondWeight := mul_nonneg on.1 (sub_nonneg.mpr second)
  have required : -(2/25)+(1/2)*t-(23/50)*t^2<0 := by
    nlinarith only [separatedScalar,boundary_lower,firstWeight,secondWeight,cosine]
  by_contra no
  have low : 1/5≤t := le_of_not_gt no
  have coefficient : 0≤1/2-(23/50)*(t+1/5) := by
    linarith only [t_high]
  have product := mul_nonneg (sub_nonneg.mpr low) coefficient
  have identity : -(2/25)+(1/2)*t-(23/50)*t^2=
      (1/625)+(t-1/5)*(1/2-(23/50)*(t+1/5)) := by ring
  nlinarith only [required,product,identity]

#print axioms tilt
end N12Compact.PositiveCornerSmallBottom
