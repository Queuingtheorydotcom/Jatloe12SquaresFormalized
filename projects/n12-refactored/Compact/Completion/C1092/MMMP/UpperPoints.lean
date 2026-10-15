import Compact.Completion.C1092.MMMP.NortheastEarlyActual
import Compact.Completion.C1092.MMMP.InwardTips

/-! The strict northwest point needed by the genuine left-wall transfer.
Both canonical signs are covered. The negative sign's small angle is
derived from the actual northeast support, before any top-origin premise. -/
namespace N12Compact.C1092MMMPUpperPoints
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MMMPEntrance C1092MMMPOrigins
open C1092MMMPPointCore C977CornerCubic
set_option Elab.async false

private theorem positive (C : OpenSquare) (cn : Normal C.c C.s) (side : 1<C.side)
    (origin : C.Inside 0 0) (diagonal : C.Inside (-1/2) (1/2))
    (north : C.Inside 0 (1/2)) (long : C.Inside (-61/100) (61/100))
    (foreign : ¬C.Inside (7/50) (1/2)) : C.Inside (-81/100) (1/5) := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have o : C.loU<0 ∧ 0<C.loU+C.side ∧ C.loV<0 ∧ 0<C.loV+C.side := by
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero] using origin
  have cap : C.loU+C.side≤(7/50)*C.c+C.s/2 := by
    apply le_of_not_gt
    intro high
    apply foreign
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [o.1,o.2.2.1,north.2.2.2,high,cp,cn.1,cn.2.1]
  have short := short_projections C (19/20) (3/10) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [cap,side,short.2.1,diagonal.2.1,o.2.2.1,long.2.2.2,cp,cn.1,cn.2.1]

private theorem negative (C : OpenSquare) (cn : Normal C.c (-C.s)) (side : 1<C.side)
    (small : -C.s<7/50) (close : 99/100<C.c)
    (origin : C.Inside 0 0) (left : C.Inside (-1/2) 0)
    (tip : C.Inside (-1/100) (27/50)) (long : C.Inside (-61/100) (61/100))
    (foreign : ¬C.Inside (7/50) (1/2)) : C.Inside (-81/100) (1/5) := by
  have cb := normal_bounds cn
  have sn : C.s≤0 := by linarith only [cn.1]
  have cp : 0<C.c := by linarith only [close]
  have o : C.loU<0 ∧ 0<C.loU+C.side ∧ C.loV<0 ∧ 0<C.loV+C.side := by
    simpa only [OpenSquare.Inside,InBands,mul_zero,add_zero,zero_add,neg_zero] using origin
  have cap : C.loU+C.side≤(7/50)*C.c+C.s/2 := by
    apply le_of_not_gt
    intro high
    apply foreign
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [o.1,o.2.2.1,tip.2.2.2,high,close,small,cn.1]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [cap,side,left.2.1,o.2.2.1,long.2.2.2,cp,sn,close,small,cb.2.1]

theorem northwest_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 7).Inside (119/100) (11/5) := by
  classical
  let q := (owners p 7).translated 2 2
  obtain ⟨C,cp,canon,shape,inside,_⟩ := ClosedFrames.canonical_frame q
  have actual (x y : ℝ) : C.Inside x y ↔ (owners p 7).Inside (2+x) (2+y) :=
    (inside x y).trans (inside_translated_iff _ _ _ _ _)
  have side : 1<C.side := by rw [shape]; exact side_gt p 7
  have origin : C.Inside 0 0 := by
    apply (actual _ _).mpr
    norm_num
    exact northwest_center p hf hb
  have long : C.Inside (-61/100) (61/100) := by
    apply (actual _ _).mpr
    norm_num
    exact northwest_long_diagonal p hf hb
  have foreign : ¬C.Inside (7/50) (1/2) := by
    intro own
    have h := (actual _ _).mp own
    norm_num at h
    exact owners_disjoint p hf 7 6 (by decide) _ _
      ⟨h,C1092MMMPNortheastEarlyActual.upper_point p hf hb⟩
  have result : C.Inside (-81/100) (1/5) := by
    by_cases sign : 0≤C.s
    · have cn : Normal C.c C.s := ⟨sign,by simpa only [abs_of_nonneg sign] using canon,C.unit_normal⟩
      exact positive C cn side origin
        (by apply (actual _ _).mpr; norm_num; exact northwest_diagonal p hf hb)
        (by apply (actual _ _).mpr; norm_num; exact northwest_north p hf hb) long foreign
    · have sn : C.s≤0 := (lt_of_not_ge sign).le
      have cn : Normal C.c (-C.s) := ⟨by linarith only [sn],
        by simpa only [abs_of_nonpos sn] using canon,by nlinarith only [C.unit_normal]⟩
      have small := C1092MMMPNortheastEarlyActual.small_northwest p hf hb C shape actual cn
      exact negative C cn side small.1 small.2 origin
        (by apply (actual _ _).mpr; norm_num; exact northwest_left p hf hb)
        (by apply (actual _ _).mpr; norm_num; exact C1092MMMPInwardTips.second_tip p hf hb)
        long foreign
  have h := (actual _ _).mp result
  norm_num at h
  exact h

#print axioms northwest_point
end N12Compact.C1092MMMPUpperPoints
