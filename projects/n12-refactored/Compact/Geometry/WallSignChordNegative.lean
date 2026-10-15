import Compact.Geometry.WallSignChordScalars

/-! The negative canonical orientation in C1092-WALL-SIGN-CHORD.
The zero sine case is handled explicitly in the upper-u comparison. -/
namespace N12Compact.WallSignChord
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem negative_point (q : OpenSquare) (s r : ℝ) (signed : q.s= -s)
    (ha : 1<q.side) (cn : 0≤q.c) (sn : 0≤s) (order : s≤q.c)
    (wall : q.side*(q.c+s)/2-1≤centerX q)
    (sign : 0≤centerY q)
    (marker : q.Inside (-43/500) 0)
    (missing : ¬q.Inside (13/20) (7/20))
    (rlow : 11/50≤r) (rhigh : r≤39/100) : q.Inside 0 r := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  obtain ⟨clow,c1,strong,approx⟩ := canonical_bounds q.c s cn sn order unit
  have cp : 0<q.c := by linarith only [clow]
  have rp : 0<r := by linarith only [rlow]
  have gaps := wall_gaps q.c s r cp sn unit rhigh
  have center := center_coordinates q
  rw [signed] at center
  have p := marker
  dsimp [OpenSquare.Inside,InBands] at p
  rw [signed] at p
  have lowerV : q.loV<q.c*r := by
    have product := mul_pos cp rp
    nlinarith only [p.2.2.1,product,sn]
  have upperV : q.c*r<q.loV+q.side := by
    apply lt_of_not_ge
    intro fail
    have weightedWall := mul_nonneg sn (sub_nonneg.mpr wall)
    have weightedSign := mul_nonneg cp.le sign
    have coefficient : 0<1+s*(q.c+s) := by positivity
    have strict := mul_pos (sub_pos.mpr ha) coefficient
    nlinarith only [weightedWall,weightedSign,center.2,fail,strict,gaps.2]
  have upperU : -s*r<q.loU+q.side := by
    apply lt_of_not_ge
    intro fail
    have small : r*s<(43/500)*q.c := by nlinarith only [p.2.1,fail]
    have pWeight := mul_nonneg sn (sub_nonneg.mpr p.2.2.1.le)
    have uWeight := mul_nonneg cp.le (sub_nonneg.mpr fail)
    have centerIdentity : centerX q=q.c*(q.loU+q.side/2)+s*(q.loV+q.side/2) := by
      simp only [centerX,signed,neg_mul,sub_neg_eq_add]
    have bound : q.side*q.c≤1-(43/500)*s^2-r*q.c*s := by
      nlinarith only [pWeight,uWeight,wall,centerIdentity]
    by_cases zero : s=0
    · have cEq : q.c=1 := by rw [zero] at unit; nlinarith only [unit,cp]
      rw [zero,cEq] at bound
      nlinarith only [bound,ha]
    · have sp : 0<s := by
        rcases sn.eq_or_lt with eq | pos
        · exact (zero eq.symm).elim
        · exact pos
      have margin := negative_u_margin q.c s r cp sp approx rlow small
      have excess := mul_pos (sub_pos.mpr ha) cp
      nlinarith only [bound,margin,excess]
  have lowerU : q.loU< -s*r := by
    apply lt_of_not_ge
    intro fail
    have nLowerU : q.loU<q.c*(13/20)-s*(7/20) := by
      have product := mul_nonneg (by norm_num : (0:ℝ)≤7/20) (sub_nonneg.mpr order)
      nlinarith only [p.1,product,cp]
    have nLowerV : q.loV<s*(13/20)+q.c*(7/20) := by
      nlinarith only [p.2.2.1,sn,cp]
    have nUpperU : q.c*(13/20)-s*(7/20)<q.loU+q.side := by
      apply lt_of_not_ge
      intro exit
      have short := (short_projections q (13/20) (-1/25) (by norm_num)).2.1
      rw [signed] at short
      have bound := mul_nonneg sn (sub_nonneg.mpr rhigh)
      nlinarith only [exit,fail,short,bound,ha]
    have nUpperV : q.loV+q.side≤s*(13/20)+q.c*(7/20) := by
      apply le_of_not_gt
      intro own
      apply missing
      simpa only [OpenSquare.Inside,InBands,signed,neg_mul,neg_neg,
        sub_eq_add_neg] using
        (show q.loU<q.c*(13/20)-s*(7/20) ∧
          q.c*(13/20)-s*(7/20)<q.loU+q.side ∧
          q.loV<s*(13/20)+q.c*(7/20) ∧
          s*(13/20)+q.c*(7/20)<q.loV+q.side from
            ⟨nLowerU,nUpperU,nLowerV,own⟩)
    have uWeight := mul_nonneg sn (sub_nonneg.mpr fail)
    have vWeight := mul_nonneg cp.le (sub_nonneg.mpr nUpperV)
    have sideWeight := mul_pos (sub_pos.mpr ha) (add_pos_of_pos_of_nonneg cp sn)
    have rWeight := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr rhigh)
    have margin := quadratic_margin_transpose q.c s cp
    have identity : centerY q= -s*(q.loU+q.side/2)+q.c*(q.loV+q.side/2) := by
      simp only [centerY,signed]
    nlinarith only [uWeight,vWeight,sideWeight,rWeight,margin,strong,unit,identity,sign]
  simpa only [OpenSquare.Inside,InBands,signed,mul_zero,neg_mul,neg_neg,
    add_zero,zero_add] using
    (show q.loU< -s*r ∧ -s*r<q.loU+q.side ∧
      q.loV<q.c*r ∧ q.c*r<q.loV+q.side from ⟨lowerU,upperU,lowerV,upperV⟩)

end
end N12Compact.WallSignChord
