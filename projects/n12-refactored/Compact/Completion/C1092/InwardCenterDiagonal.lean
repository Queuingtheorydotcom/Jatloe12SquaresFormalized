import Compact.Completion.C1092.RigidCharts
import S12.ShortCluster

/-! The same actual inward square owns its complete diagonal interval.
The two omitted neighboring markers permit weak face contact. No wall,
orientation restriction, or upper side bound is part of the theorem. -/
namespace N12Compact.C1092InwardCenterDiagonal
open S12 S12Pilot C1092RigidCharts
set_option Elab.async false

private theorem canonical (q : OpenSquare) (side : 1 < q.side)
    (cosine : 0 < q.c) (sine : q.s ≤ 0) (order : -q.s ≤ q.c)
    (origin : q.Inside 0 0) (marker : q.Inside (7/20) (7/20))
    (north : ¬ q.Inside (-7/20) (7/20))
    (east : ¬ q.Inside (7/20) (-7/20))
    (k : ℝ) (lower : 7/20 ≤ k) (length : k^2 ≤ 151/400) :
    q.Inside k k := by
  classical
  have o : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,neg_zero] using origin
  have northFace : q.c*(-7/20)+q.s*(7/20) ≤ q.loU := by
    apply le_of_not_gt
    intro h
    apply north
    exact ⟨h,by linarith only [o.2.1,cosine,sine],
      by linarith only [o.2.2.1,order],
      by linarith only [marker.2.2.2,sine]⟩
  have chord := short_projections q (7/10) (-7/10) (by norm_num)
  have eastFace : -q.s*(7/20)+q.c*(-7/20) ≤ q.loV := by
    apply le_of_not_gt
    intro h
    apply east
    exact ⟨by linarith only [o.1,cosine,sine],
      by linarith only [northFace,side,chord.2.1],h,
      by linarith only [o.2.2.2,order]⟩
  have longitudinal := mul_nonneg (sub_nonneg.mpr lower)
    (show 0 ≤ q.c+q.s by linarith only [order])
  have transverse := mul_nonneg (sub_nonneg.mpr lower)
    (show 0 ≤ q.c-q.s by linarith only [cosine,sine])
  have shortN := short_projections q (k+7/20) (k-7/20)
    (by nlinarith only [length])
  have shortD := short_projections q (k-7/20) (k+7/20)
    (by nlinarith only [length])
  exact ⟨by nlinarith only [marker.1,longitudinal],
    by linarith only [northFace,side,shortN.2.1],
    by nlinarith only [marker.2.2.1,transverse],
    by linarith only [eastFace,side,shortD.2.2.2]⟩

/-- Every point of the exact diagonal interval is strict in the original
square. The endpoint is represented by its squared-length inequality. -/
theorem diagonal (q : OpenSquare) (side : 1 < q.side)
    (origin : q.Inside 0 0) (marker : q.Inside (7/20) (7/20))
    (north : ¬ q.Inside (-7/20) (7/20))
    (east : ¬ q.Inside (7/20) (-7/20))
    (k : ℝ) (lower : 7/20 ≤ k) (length : k^2 ≤ 151/400) :
    q.Inside k k := by
  obtain ⟨r,cosine,range,same,inside,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [same] using side
  have origin' := (inside _ _).mpr origin
  have marker' := (inside _ _).mpr marker
  have north' : ¬ r.Inside (-7/20) (7/20) := fun h => north ((inside _ _).mp h)
  have east' : ¬ r.Inside (7/20) (-7/20) := fun h => east ((inside _ _).mp h)
  apply (inside _ _).mp
  by_cases sign : r.s ≤ 0
  · exact canonical r side' cosine sign (by linarith only [(abs_le.mp range).1])
      origin' marker' north' east' k lower length
  · have h := canonical (swap r) side' cosine
      (by change -r.s ≤ 0; linarith only [sign])
      (by change -(-r.s) ≤ r.c; simpa only [neg_neg] using (abs_le.mp range).2)
      ((inside_swap r _ _).mpr origin') ((inside_swap r _ _).mpr marker')
      (fun h => east' ((inside_swap r _ _).mp h))
      (fun h => north' ((inside_swap r _ _).mp h)) k lower length
    exact (inside_swap r _ _).mp h

theorem point (q : OpenSquare) (side : 1 < q.side)
    (origin : q.Inside 0 0) (marker : q.Inside (7/20) (7/20))
    (north : ¬ q.Inside (-7/20) (7/20))
    (east : ¬ q.Inside (7/20) (-7/20)) : q.Inside (1/2) (1/2) :=
  diagonal q side origin marker north east (1/2) (by norm_num) (by norm_num)

theorem long_point (q : OpenSquare) (side : 1 < q.side)
    (origin : q.Inside 0 0) (marker : q.Inside (7/20) (7/20))
    (north : ¬ q.Inside (-7/20) (7/20))
    (east : ¬ q.Inside (7/20) (-7/20)) : q.Inside (61/100) (61/100) :=
  diagonal q side origin marker north east (61/100) (by norm_num) (by norm_num)

#print axioms diagonal
end N12Compact.C1092InwardCenterDiagonal
