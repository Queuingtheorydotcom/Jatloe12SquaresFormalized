import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The asymmetric two-short-gaps outward-corner obstruction from the
current mathematical route. Every orientation and every weak face exit
is covered, with no wall, containment or upper-side hypothesis. -/
namespace N12Compact.C1092CornerTwoGaps
open S12 S12Pilot
set_option Elab.async false

private theorem positive_impossible (q : OpenSquare) (ha : 1 < q.side)
    (hc : 0 < q.c) (hs : 0 ≤ q.s) (order : q.s ≤ q.c)
    (r t : ℝ) (rp : 0 < r) (ru : r < 2/5) (tp : 0 < t) (tu : t < 2/5)
    (gap : (1-r)^2+(1-t)^2 ≤ 1)
    (marker : q.Inside (47/20) (47/20))
    (A : q.Inside (12/5) 3) (B : q.Inside 3 (12/5))
    (F : ¬ q.Inside (2+r) 3) (G : ¬ q.Inside 3 (2+t))
    (K : ¬ q.Inside 3 3) : False := by
  classical
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,hc]
  have ku0 : q.loU < q.c*3+q.s*3 := by linarith only [A.1,hc]
  have kv0 : q.loV < -q.s*3+q.c*3 := by linarith only [B.2.2.1,hc]
  have kv1 : -q.s*3+q.c*3 < q.loV+q.side := by linarith only [A.2.2.2,hs]
  have ku1 : q.loU+q.side ≤ q.c*3+q.s*3 :=
    le_of_not_gt (fun h => K ⟨ku0,h,kv0,kv1⟩)
  have tg0 := mul_nonneg hs (sub_nonneg.mpr tu.le)
  have tg1 := mul_pos hc (sub_pos.mpr tu)
  have tg2 := mul_nonneg hs tp.le
  have gu0 : q.loU < q.c*3+q.s*(2+t) := by
    nlinarith only [marker.1,hc,order,tg2]
  have gu1 : q.c*3+q.s*(2+t) < q.loU+q.side := by
    nlinarith only [B.2.1,tg0]
  have gv1 : -q.s*3+q.c*(2+t) < q.loV+q.side := by
    nlinarith only [B.2.2.2,tg1]
  have gv0 : -q.s*3+q.c*(2+t) ≤ q.loV :=
    le_of_not_gt (fun h => G ⟨gu0,gu1,h,gv1⟩)
  have rf0 := mul_pos hc (sub_pos.mpr ru)
  have rf1 := mul_nonneg hs (sub_nonneg.mpr ru.le)
  have fu1 : q.c*(2+r)+q.s*3 < q.loU+q.side := by
    nlinarith only [A.2.1,rf0]
  have fv0 : q.loV < -q.s*(2+r)+q.c*3 := by
    nlinarith only [A.2.2.1,rf1]
  have fu0 : q.loU < q.c*(2+r)+q.s*3 := by
    by_contra bad
    have face : q.c*(2+r)+q.s*3 ≤ q.loU := le_of_not_gt bad
    have rProduct := mul_nonneg rp.le hc.le
    nlinarith only [face,ku1,ha,cu,rProduct]
  have fv1 : q.loV+q.side ≤ -q.s*(2+r)+q.c*3 :=
    le_of_not_gt (fun h => F ⟨fu0,fu1,fv0,h⟩)
  have short := short_projections q (1-t) (1-r) (by nlinarith only [gap])
  nlinarith only [gv0,fv1,ha,short.2.1]

private noncomputable def swapped (q : OpenSquare) : OpenSquare where
  c := q.c
  s := -q.s
  loU := q.loV
  loV := q.loU
  side := q.side
  unit_normal := by nlinarith [q.unit_normal]
  side_pos := q.side_pos

private theorem swapped_inside (q : OpenSquare) (x y : ℝ) :
    (swapped q).Inside x y ↔ q.Inside y x := by
  dsimp [swapped,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨h0,h1,h2,h3⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem impossible (q : OpenSquare) (ha : 1 < q.side)
    (r t : ℝ) (rp : 0 < r) (ru : r < 2/5) (tp : 0 < t) (tu : t < 2/5)
    (gap : (1-r)^2+(1-t)^2 ≤ 1)
    (marker : q.Inside (47/20) (47/20))
    (A : q.Inside (12/5) 3) (B : q.Inside 3 (12/5))
    (F : ¬ q.Inside (2+r) 3) (G : ¬ q.Inside 3 (2+t))
    (K : ¬ q.Inside 3 3) : False := by
  obtain ⟨w,hc,range,side,inside,_⟩ := ClosedFrames.canonical_frame q
  have wa : 1 < w.side := by simpa only [side] using ha
  have wm := (inside _ _).mpr marker
  have wA := (inside _ _).mpr A
  have wB := (inside _ _).mpr B
  have wF : ¬ w.Inside (2+r) 3 := fun h => F ((inside _ _).mp h)
  have wG : ¬ w.Inside 3 (2+t) := fun h => G ((inside _ _).mp h)
  have wK : ¬ w.Inside 3 3 := fun h => K ((inside _ _).mp h)
  by_cases hs : 0 ≤ w.s
  · exact positive_impossible w wa hc hs
      (by simpa only [abs_of_nonneg hs] using range)
      r t rp ru tp tu gap wm wA wB wF wG wK
  · exact positive_impossible (swapped w) wa hc
      (by dsimp [swapped]; linarith only [hs])
      (by simpa only [swapped,abs_of_neg (lt_of_not_ge hs)] using range)
      t r tp tu rp ru (by nlinarith only [gap])
      ((swapped_inside _ _ _).mpr wm) ((swapped_inside _ _ _).mpr wB)
      ((swapped_inside _ _ _).mpr wA)
      (fun h => wG ((swapped_inside _ _ _).mp h))
      (fun h => wF ((swapped_inside _ _ _).mp h))
      (fun h => wK ((swapped_inside _ _ _).mp h))

#print axioms impossible
end N12Compact.C1092CornerTwoGaps
