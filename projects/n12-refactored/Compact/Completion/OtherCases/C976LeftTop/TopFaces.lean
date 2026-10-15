import Compact.Completion.OtherCases.C976LeftTop.Directions

/-! Section 2: the literal omitted right point of W exits below W.
The identical full-interval scalar estimates are shared with the ordinary
left/top theorem; only the original weaker C976 angle premise is used. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open OrdinaryLeftTop
set_option Elab.async false

theorem top_lowerV (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (w : QuadrantData W) (same : N.side=W.side)
    (axes : upper N N.c N.s≤lower W N.c N.s ∨
      upper N W.c W.s≤lower W W.c W.s) : W.c-(63/50)*W.s≤W.loV := by
  have coeff := coefficients N W n w
  have side : 1<W.side := by simpa only [←same] using n.side
  have bounds := ShallowTopExitScalars.wall_bounds W.c W.s w.cosine w.sine W.unit_normal w.slope
  have origin := t.origin
  have marker := t.marker
  simp only [OpenSquare.Inside,InBands,mul_one] at origin marker
  have noUpper : ¬W.loU+W.side≤(63/50)*W.c+W.s := by
    intro cap
    have gap : (43/500)*W.s<(13/50)*W.c := by linarith only [cap,marker.2.1]
    have lowerC := ShallowTopExitScalars.cosine_lower W.c W.s w.cosine w.sine W.unit_normal gap
    rcases axes with leftAxis | topAxis
    · have residual := ShallowTopExitScalars.upper_exit_residual N.c N.s W.c W.s
        n.cosine n.angleLower.le w.cosine w.sine W.unit_normal lowerC.le bounds.1
      have capWeight := mul_le_mul_of_nonneg_left cap coeff.1.le
      have originWeight := mul_lt_mul_of_pos_left origin.2.2.2 coeff.2
      have extra := mul_pos (sub_pos.mpr side) coeff.1
      have support : lower W N.c N.s<
          alpha N W*((63/50)*W.c+W.s-1)-beta N W*(W.c-W.s) := by
        rw [lower_left_normal N W n w]
        nlinarith only [capWeight,originWeight,extra]
      have identity : alpha N W*((63/50)*W.c+W.s-1)-beta N W*(W.c-W.s)=
          (13/20)*N.c+(7/20)*N.s+
          N.c*ShallowTopExitScalars.F W.c+N.s*ShallowTopExitScalars.G W.c W.s := by
        dsimp only [alpha,beta,ShallowTop.alpha,ShallowTop.gamma,
          ShallowTopExitScalars.F,ShallowTopExitScalars.G]
        linear_combination (N.c+N.s)*W.unit_normal
      have markerBound := (strict_bounds N _ _ N.c N.s N.unit_normal n.marker).2
      linarith only [support,identity,residual,markerBound,leftAxis]
    · have projection := ShallowTopExitScalars.marker_projection W.c W.s W.unit_normal
      have markerBound := (strict_bounds N _ _ W.c W.s W.unit_normal n.marker).2
      rw [(ownU W).1] at topAxis
      linarith only [cap,side,projection,markerBound,topAxis]
  apply le_of_not_gt
  intro low
  apply t.missing
  simp only [OpenSquare.Inside,InBands,mul_one]
  exact ⟨by linarith only [origin.1,w.cosine],lt_of_not_ge noUpper,
    by linarith only [low],by linarith only [origin.2.2.2,w.sine]⟩

/-- S times the manuscript's W-star; no division is needed. -/
def target (N W : OpenSquare) : ℝ :=
  N.c*(W.c-1+W.s*(63/50-W.c))+N.s*W.s*(2-W.s)

theorem lower_support_strict (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (w : QuadrantData W) (same : N.side=W.side)
    (face : W.c-(63/50)*W.s≤W.loV) : W.s*lower W N.c N.s<target N W := by
  have coeff := coefficients N W n w
  have wall := ShallowTop.top_wall_faces W t w
  have side : 1<W.side := by simpa only [←same] using n.side
  have slackWall := mul_nonneg coeff.1.le (sub_nonneg.mpr wall)
  have slackFace := mul_nonneg n.cosine.le (sub_nonneg.mpr face)
  have extra := mul_pos (sub_pos.mpr side)
    (show 0<alpha N W*W.s+N.c by positivity)
  have identity : target N W-W.s*lower W N.c N.s=
      alpha N W*(2-W.s*(W.loU+W.side)-W.c*(W.loV+W.side))+
      N.c*(W.loV-(W.c-(63/50)*W.s))+
      (W.side-1)*(alpha N W*W.s+N.c) := by
    rw [lower_left_normal N W n w]
    dsimp only [target,alpha,beta,ShallowTop.alpha,ShallowTop.gamma]
    linear_combination (W.loV+W.side)*N.c*W.unit_normal
  linarith only [identity,slackWall,slackFace,extra]

theorem target_low (N W : OpenSquare) (n : LeftInput N) (w : QuadrantData W)
    (small : N.s≤(1/2)*N.c) : target N W≤W.s*((13/50)*N.c+N.s) := by
  have bounds := ShallowTopExitScalars.wall_bounds W.c W.s w.cosine w.sine W.unit_normal w.slope
  have projection := CommonCases.CanonicalProjection.before W.s W.c (4/5) (3/5) (1/2) 1
    (by nlinarith only [W.unit_normal]) (by norm_num)
    (by linarith only [w.slope,w.sine]) (by norm_num) (by norm_num)
  have first := mul_nonneg w.sine.le (sub_nonneg.mpr small)
  have last := mul_nonneg n.cosine.le
    (show 0≤1-W.c-W.s/2 by linarith only [projection])
  have bracket : N.s*W.s≤N.c*(1-W.c) := by nlinarith only [first,last]
  have gap := mul_nonneg (show 0≤1-W.s by linarith only [bounds.2.2.2])
    (sub_nonneg.mpr bracket)
  dsimp only [target]
  nlinarith only [gap]

theorem target_high (N W : OpenSquare) (n : LeftInput N) (w : QuadrantData W)
    (large : (1/2)*N.c≤N.s) : target N W≤W.s*((4/25)*N.c+(6/5)*N.s) := by
  have bounds := ShallowTopExitScalars.wall_bounds W.c W.s w.cosine w.sine W.unit_normal w.slope
  have projection := CommonCases.CanonicalProjection.before W.s W.c (4/5) (3/5) (1/2) 1
    (by nlinarith only [W.unit_normal]) (by norm_num)
    (by linarith only [w.slope,w.sine]) (by norm_num) (by norm_num)
  have first := mul_nonneg n.cosine.le
    (show 0≤1-W.c-W.s/2 by linarith only [projection])
  have scaled := mul_nonneg (show 0≤1-W.s by linarith only [bounds.2.2.2]) first
  have last := mul_nonneg (mul_nonneg w.sine.le (sub_nonneg.mpr large))
    (show 0≤W.s-4/5 by linarith only [bounds.2.1])
  dsimp only [target]
  nlinarith only [scaled,last]

end N12Compact.Completion.OtherCases.C976LeftTop
