import Compact.Geometry.WallSignChordScalars

/-! The four strict bands in the positive canonical frame, including
the axial and diagonal endpoints. Only the one real left wall is used. -/
namespace N12Compact.WallSignChord
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem positive_point (q : OpenSquare) (r : ℝ)
    (ha : 1<q.side) (cn : 0≤q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (wall : q.side*(q.c+q.s)/2-1≤centerX q)
    (sign : 0≤centerY q)
    (marker : q.Inside (-43/500) 0)
    (missing : ¬q.Inside (13/20) (7/20))
    (rlow : 11/50≤r) (rhigh : r≤39/100) : q.Inside 0 r := by
  obtain ⟨clow,c1,strong,approx⟩ := canonical_bounds q.c q.s cn sn order q.unit_normal
  have cp : 0<q.c := by linarith only [clow]
  have rp : 0<r := by linarith only [rlow]
  have rs := mul_nonneg rp.le sn
  have gaps := wall_gaps q.c q.s r cp sn q.unit_normal rhigh
  have center := center_coordinates q
  have p := marker
  dsimp [OpenSquare.Inside,InBands] at p
  have lowerU : q.loU<q.s*r := by nlinarith only [p.1,cp,rs]
  have lowerV : q.loV<q.c*r := by
    have first := mul_pos cp (show 0<r-43/500 by linarith only [rlow])
    have second := mul_nonneg (by norm_num : (0:ℝ)≤43/500) (sub_nonneg.mpr order)
    nlinarith only [p.2.2.1,first,second]
  have upperU : q.s*r<q.loU+q.side := by
    apply lt_of_not_ge
    intro fail
    have weightedWall := mul_nonneg cp.le (sub_nonneg.mpr wall)
    have weightedSign := mul_nonneg sn sign
    have coefficient : 0<1+q.c*(q.c+q.s) := by positivity
    have strict := mul_pos (sub_pos.mpr ha) coefficient
    nlinarith only [weightedWall,weightedSign,center.1,fail,strict,gaps.1]
  have upperV : q.c*r<q.loV+q.side := by
    apply lt_of_not_ge
    intro fail
    have nLowerU : q.loU<q.c*(13/20)+q.s*(7/20) := by
      nlinarith only [p.1,cp,sn]
    have nLowerV : q.loV< -q.s*(13/20)+q.c*(7/20) := by
      apply lt_of_not_ge
      intro exit
      have short := (short_projections q (13/20) (-1/25) (by norm_num)).2.2.1
      have bound := mul_nonneg cp.le (sub_nonneg.mpr rhigh)
      nlinarith only [exit,fail,short,bound,ha]
    have nUpperV : -q.s*(13/20)+q.c*(7/20)<q.loV+q.side := by
      apply lt_of_not_ge
      intro exit
      have first := mul_nonneg sn (sub_nonneg.mpr p.1.le)
      have second := mul_nonneg cp.le (sub_nonneg.mpr exit)
      have width := mul_nonneg (sub_nonneg.mpr ha.le) (sub_nonneg.mpr order)
      have cCoefficient : (7/20)*q.c-1/2<0 := by linarith only [c1]
      have sCoefficient : 1/2-(92/125)*q.c<0 := by linarith only [clow]
      have strict := mul_neg_of_pos_of_neg cp cCoefficient
      have nonpositive := mul_nonpos_of_nonneg_of_nonpos sn sCoefficient.le
      have identity : centerY q=q.s*(q.loU+q.side/2)+q.c*(q.loV+q.side/2) := rfl
      nlinarith only [first,second,width,strict,nonpositive,identity,sign]
    have nUpperU : q.loU+q.side≤q.c*(13/20)+q.s*(7/20) := by
      apply le_of_not_gt
      intro own
      exact missing ⟨nLowerU,own,nLowerV,nUpperV⟩
    have uWeight := mul_nonneg sn (sub_nonneg.mpr nUpperU)
    have vWeight := mul_nonneg cp.le (sub_nonneg.mpr fail)
    have sideWeight := mul_pos (sub_pos.mpr ha) (add_pos_of_pos_of_nonneg cp sn)
    have rWeight := mul_nonneg (sq_nonneg q.c) (sub_nonneg.mpr rhigh)
    have margin := quadratic_margin q.c q.s cp sn
    have identity : centerY q=q.s*(q.loU+q.side/2)+q.c*(q.loV+q.side/2) := rfl
    nlinarith only [uWeight,vWeight,sideWeight,rWeight,margin,strong,
      q.unit_normal,identity,sign]
  simpa only [OpenSquare.Inside,InBands,mul_zero,neg_mul,add_zero,zero_add] using
    (show q.loU<q.s*r ∧ q.s*r<q.loU+q.side ∧
      q.loV<q.c*r ∧ q.c*r<q.loV+q.side from ⟨lowerU,upperU,lowerV,upperV⟩)

end
end N12Compact.WallSignChord
