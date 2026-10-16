import Compact.Completion.OtherCases.TopOnlyQuadrantProfile
import Mathlib.Tactic.Positivity

/-! Whole-quadrant rational bounds from the four true top-only faces.
Both widths are used; the half-angle interval and the full support margin
are exact factorizations, without an ordering of the normal components. -/
namespace N12Compact.Completion.OtherCases.TopOnlyQuadrantScalars
open C1092WallProfileScalars
set_option Elab.async false

theorem bounds (d r : ℝ) (dp : 0<d) (rp : 0<r) (unit : d^2+r^2=1)
    (uWidth : 1<d+(11/25)*r) (vWidth : 1<(37/50)*d+r) :
    13/87<half d r ∧ half d r<11/25 ∧ 2/3<d ∧ r<3/4 ∧
      4831/3869≤d+r ∧ d+r<10/7 ∧ 1<d+r-(37/50)*d*r ∧
      r-d-13/50-(37/50)*r^2<0 := by
  have data := quarter_data d r dp.le rp.le unit
  let z := half d r
  have zu := SharpPointScalars.half_upper d r (11/25) dp rp unit uWidth
  have rUpper : r≤1 := by nlinarith only [unit,sq_nonneg d,rp]
  have zOne : z<1 := by
    unfold z half
    exact (div_lt_one (by linarith only [dp])).mpr (by linarith only [rUpper,dp])
  have scale : 0<1+z^2 := by positivity
  have scaled := mul_pos scale (sub_pos.mpr vWidth)
  have identity : (1+z^2)*((37/50)*d+r-1)=
      (1-z)*((87/50)*z-13/50) := by
    calc
      _ = (37/50)*((1+z^2)*d)+(1+z^2)*r-(1+z^2) := by ring
      _ = _ := by rw [data.2.2.2.1,data.2.2.2.2]; ring
  rw [identity] at scaled
  have gap := (mul_pos_iff_of_pos_left (sub_pos.mpr zOne)).mp scaled
  have zl : 13/87<z := by linarith only [gap]
  have cross := SharpPointScalars.half_before d r (252/373) (275/373) (11/25)
    dp rp.le unit (by norm_num) (by norm_num) (by norm_num) zu.le
  have product := mul_nonneg (show 0≤275*d-252*r by linarith only [cross])
    (show 0≤275*d+252*r by linarith only [dp,rp])
  have dLarge : 2/3<d := by
    by_contra bad
    have small : d≤2/3 := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤2/3+d by linarith only [dp])
    nlinarith only [product,unit,square]
  have rSmall : r<3/4 := by
    by_contra bad
    have large : 3/4≤r := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤r+3/4 by linarith only [rp])
    nlinarith only [product,unit,square]
  have factor := mul_pos (sub_pos.mpr zl)
    (show 0<37/50-z by linarith only [zu])
  have sumIdentity : (1+z^2)*(d+r-4831/3869)=
      (8700/3869)*(z-13/87)*(37/50-z) := by
    calc
      _ = (1+z^2)*d+(1+z^2)*r-(4831/3869)*(1+z^2) := by ring
      _ = _ := by rw [data.2.2.2.1,data.2.2.2.2]; ring
  have sumScaled : 0<(1+z^2)*(d+r-4831/3869) := by
    rw [sumIdentity]
    nlinarith only [factor]
  have sumGap := (mul_pos_iff_of_pos_left scale).mp sumScaled
  have sumLower : 4831/3869≤d+r := by linarith only [sumGap]
  have sumUpper : d+r<10/7 := by
    by_contra bad
    have high : 10/7≤d+r := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr high)
      (show 0≤d+r+10/7 by linarith only [dp,rp])
    nlinarith only [square,unit,sq_nonneg (d-r)]
  have interval := mul_nonneg (sub_nonneg.mpr sumLower) (sub_nonneg.mpr sumUpper.le)
  have support : 1<d+r-(37/50)*d*r := by
    nlinarith only [interval,unit,sumLower]
  have other : r-d-13/50-(37/50)*r^2<0 := by
    nlinarith only [dLarge,rSmall,sq_nonneg r]
  exact ⟨zl,zu,dLarge,rSmall,sumLower,sumUpper,support,other⟩

theorem profile_bounds (q : S12Pilot.OpenSquare) (side : 1<q.side)
    (profile : TopOnlyQuadrantProfile.Data q) :
    13/87<half q.c (-q.s) ∧ half q.c (-q.s)<11/25 ∧ 2/3<q.c ∧ -q.s<3/4 ∧
      4831/3869≤q.c-q.s ∧ q.c-q.s<10/7 ∧
      1<q.c-q.s+(37/50)*q.c*q.s ∧
      -q.s-q.c-13/50-(37/50)*q.s^2<0 := by
  have data := bounds q.c (-q.s) profile.cosine_pos
    (by linarith only [profile.sine_neg])
    (by simpa only [neg_sq] using q.unit_normal)
    (by linarith only [profile.lowerU,profile.upperU,side])
    (by linarith only [profile.lowerV,profile.upperV,side])
  simpa only [neg_sq,mul_neg,sub_eq_add_neg,neg_neg] using data

#print axioms bounds
#print axioms profile_bounds
end N12Compact.Completion.OtherCases.TopOnlyQuadrantScalars
