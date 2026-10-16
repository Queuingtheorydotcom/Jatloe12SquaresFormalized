import Compact.Geometry.WallLowerReach
import Compact.Completion.C1092.RigidCharts
import S12.Convex

/-! The one-wall specialization of the completed .56 reach argument.
WallLowerReach's calculation uses only its leftmost vertex bound; this
copy exposes precisely that wall, without assuming a full container.
The last theorem is C1089-CONTINUOUS-REDUCTION Theorem 3, first step.
Source only, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousReach
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

private theorem positive_point (q : OpenSquare) (ha : 1<q.side)
    (hc : 0≤q.c) (hs : 0≤q.s)
    (wall : 0≤q.c*q.loU-q.s*(q.loV+q.side))
    (hP : q.Inside (457/500) 2) (hQ : q.Inside 1 (12/5))
    (hW : ¬q.Inside 1 (87/50))
    (hD : ¬q.Inside (87/50) 2) : q.Inside 1 (64/25) := by
  have hcs : 0≤q.c*q.s := mul_nonneg hc hs
  have hsum : 1≤q.c+q.s := by nlinarith only [q.unit_normal,hcs,hc,hs]
  have hsumhi : q.c+q.s≤10/7 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),hc,hs]
  have hsumstrong : 1+(41/50)*q.c*q.s≤q.c+q.s := by
    nlinarith only [q.unit_normal,hcs,
      mul_nonneg (sub_nonneg.mpr hsumhi) (sub_nonneg.mpr hsum)]
  have targetUlo : q.loU<q.c+q.s*(64/25) := by nlinarith only [hP.1,hc,hs]
  have targetVlo : q.loV< -q.s+q.c*(64/25) := by nlinarith only [hQ.2.2.1,hc]
  have dUlo : q.loU<q.c*(87/50)+q.s*2 := by nlinarith only [hP.1,hc]
  have dVhi : -q.s*(87/50)+q.c*2<q.loV+q.side := by
    nlinarith only [hQ.2.2.2,hc,hs]
  have dmodes : q.loU+q.side≤q.c*(87/50)+q.s*2 ∨
      -q.s*(87/50)+q.c*2≤q.loV := by
    by_cases hu : q.loU+q.side≤q.c*(87/50)+q.s*2
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => hD ⟨dUlo,lt_of_not_ge hu,hv,dVhi⟩))
  have wUhi : q.c+q.s*(87/50)<q.loU+q.side := by nlinarith only [hQ.2.1,hs]
  have wVhi : -q.s+q.c*(87/50)<q.loV+q.side := by nlinarith only [hP.2.2.2,hc,hs]
  have wmodes : q.c+q.s*(87/50)≤q.loU ∨ -q.s+q.c*(87/50)≤q.loV := by
    by_cases hu : q.c+q.s*(87/50)≤q.loU
    · exact Or.inl hu
    · exact Or.inr (le_of_not_gt (fun hv => hW
        ⟨by simpa only [mul_one] using lt_of_not_ge hu,
          by simpa only [mul_one] using wUhi,by simpa only [mul_one] using hv,
          by simpa only [mul_one] using wVhi⟩))
  have targetW := short_projections q 0 (41/50) (by norm_num)
  rcases wmodes with wu | wv
  · have gap := (short_projections q (37/50) (13/50) (by norm_num)).2.1
    have dv : -q.s*(87/50)+q.c*2≤q.loV := by
      rcases dmodes with du | dv
      · exfalso; linarith only [wu,du,gap,ha]
      · exact dv
    have targetD := (short_projections q (-37/50) (14/25) (by norm_num)).2.2.2
    exact ⟨by simpa only [mul_one] using targetUlo,
      by simpa only [mul_one] using (show q.c+q.s*(64/25)<q.loU+q.side by
        linarith only [wu,targetW.2.1,ha]),
      by simpa only [mul_one] using targetVlo,
      by simpa only [mul_one] using (show -q.s+q.c*(64/25)<q.loV+q.side by
        linarith only [dv,targetD,ha])⟩
  · have vwall := mul_nonneg hs (sub_nonneg.mpr wv)
    have strict := mul_pos (sub_pos.mpr ha) (show 0<q.c+q.s by linarith only [hsum])
    have targetUhi : q.c+q.s*(64/25)<q.loU+q.side := by
      apply lt_of_not_ge
      intro above
      have product := mul_nonneg hc (sub_nonneg.mpr above)
      nlinarith only [wall,vwall,strict,product,hsumstrong,q.unit_normal]
    exact ⟨by simpa only [mul_one] using targetUlo,
      by simpa only [mul_one] using targetUhi,
      by simpa only [mul_one] using targetVlo,
      by simpa only [mul_one] using (show -q.s+q.c*(64/25)<q.loV+q.side by
        linarith only [wv,targetW.2.2.2,ha])⟩

theorem left_point (q : OpenSquare) (side : 1<q.side)
    (wall : ∀ x y,q.Inside x y → 0≤x)
    (marker : q.Inside (457/500) 2) (anchor : q.Inside 1 (12/5))
    (low : ¬q.Inside 1 (87/50)) (inward : ¬q.Inside (87/50) 2) :
    q.Inside 1 (64/25) := by
  obtain ⟨r,hc,hs,shape,_,_,inside⟩ := exists_positive_frame q
  have vertex : 0≤r.c*r.loU-r.s*(r.loV+r.side) := by
    apply affine_endpoint_nonnegative r.side (r.c+r.s) _ r.side_pos
    intro e positive small
    let u := r.loU+e
    let v := r.loV+r.side-e
    have own : r.Inside (r.c*u-r.s*v) (r.s*u+r.c*v) := by
      apply (inside_iff_rotated_box r _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp only [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have bound := wall _ _ ((inside _ _).mp own)
    dsimp only [u,v] at bound
    nlinarith only [bound]
  exact (inside _ _).mp (positive_point r (by simpa only [shape] using side)
    hc hs vertex ((inside _ _).mpr marker) ((inside _ _).mpr anchor)
    (fun own => low ((inside _ _).mp own)) (fun own => inward ((inside _ _).mp own)))

/-- B's actual upper wall and the foreign C inward point give both the
.56 point and the halfway point. The excluded F remains a separate premise. -/
theorem bottom_points (B C : OpenSquare) (side : 1<B.side)
    (wall : ∀ x y,B.Inside x y → y≤2)
    (marker : B.Inside 0 (543/500)) (anchor : B.Inside (2/5) 1)
    (missing : ¬B.Inside (-13/50) 1) (inward : C.Inside 0 (13/50))
    (apart : ∀ x y,¬(B.Inside x y ∧ C.Inside x y)) :
    B.Inside (14/25) 1 ∧ B.Inside (1/2) 1 := by
  let R := C1092RigidCharts.translate (pullX (pullSwap B)) 2 (-2)
  have chart (x y : ℝ) : R.Inside x y↔B.Inside (y-2) (2-x) := by
    dsimp only [R]
    rw [C1092RigidCharts.inside_translate,inside_pullX,inside_pullSwap]
    congr 2 <;> ring
  have far := left_point R side
    (by
      intro x y own
      have bound := wall _ _ ((chart _ _).mp own)
      linarith only [bound])
    (by norm_num [chart]; exact marker)
    (by norm_num [chart]; exact anchor)
    (by norm_num [chart]; simpa only [neg_div] using missing)
    (by
      intro own
      have actual := (chart _ _).mp own
      norm_num at actual
      exact apart _ _ ⟨actual,inward⟩)
  have actual := (chart _ _).mp far
  norm_num at actual
  refine ⟨actual,?_⟩
  convert inside_segment B (2/5) 1 (14/25) 1 (5/8)
    anchor actual (by norm_num) (by norm_num) using 1 <;> norm_num

#print axioms left_point
#print axioms bottom_points
end N12Compact.Completion.OtherCases.C1089.ContinuousReach
