import Compact.Completion.C1092.MMMP.UpperPoints
import Compact.Completion.C1092.MixedWideCrossing
import Compact.Completion.C1092.RigidCharts

/-! The actual left wall must own G1. A hypothetical opposite reach
gives its genuine mixed-wall profile; the strict northwest point and
the true left wall then contradict that same square's full faces. -/
namespace N12Compact.C1092MMMPLeftFar
open S12 S12Pilot ABTransverse ThreeSquare C1092RigidCharts
open C1092WallCycle C1092WallSymmetry C1092AuxiliaryCover C1092MMMPEntrance C1092MMMPOrigins
set_option Elab.async false

theorem wide_impossible (B : OpenSquare) (side : 1<B.side)
    (cp : 0<B.c) (sn : B.s<0) (order : -B.s<B.c) (wide : 5/4<B.c-B.s)
    (M : B.Inside (-43/500) 0) (O : B.Inside 0 0) (T : B.Inside 0 (39/100))
    (Z : ¬B.Inside (19/100) (1/5))
    (upperV : B.loV+B.side≤(2/5)*B.c)
    (wall : ∀ x y, B.Inside x y → -1≤x) : False := by
  have cnon := cp.le
  have tnon : 0≤ -B.s := by linarith only [sn]
  have cn : C977CornerCubic.Normal B.c (-B.s) := ⟨tnon,order.le,by nlinarith only [B.unit_normal]⟩
  have cb := C977CornerCubic.normal_bounds cn
  have upperU : B.loU+B.side≤(19/100)*B.c+(1/5)*B.s := by
    apply le_of_not_gt
    intro high
    apply Z
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [M.1,O.2.2.1,T.2.2.2,high,cp,sn,order]
  have bound := square_support_bound B (-1) 0 1
    (by intro x y own; have h := wall x y own; linarith only [h])
  norm_num [squareRadius,abs_of_pos cp,abs_of_neg sn] at bound
  have lower : -1≤B.c*B.loU-B.s*B.loV := by
    dsimp [centerX] at bound
    nlinarith only [bound]
  have first := mul_le_mul_of_nonneg_left upperU cnon
  have last := mul_le_mul_of_nonneg_left upperV tnon
  have strict := mul_pos (sub_pos.mpr side)
    (show 0<B.c-B.s by linarith only [wide])
  have needed : B.c-B.s<1+(19/100)*B.c^2-(1/5)*B.c*B.s := by
    nlinarith only [lower,first,last,strict]
  have cosine := mul_nonneg cnon (sub_nonneg.mpr cb.2.1)
  have relation : 2*(-B.s)*B.c=(B.c-B.s)^2-1 := by nlinarith only [B.unit_normal]
  have weak : B.c-B.s<109/100+(B.c-B.s)^2/10 := by
    nlinarith only [needed,cosine,relation,cb.2.1]
  have scalar := mul_nonneg (show 0≤B.c-B.s-5/4 by linarith only [wide])
    (show 0≤1-(B.c-B.s+5/4)/10 by linarith only [cb.2.2.2.2.2])
  nlinarith only [scalar,weak]

theorem point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmp) : (owners p 8).Inside 1 (12/5) := by
  classical
  by_contra omitted
  have lower : (owners p 8).Inside 1 (8/5) := by
    rcases left_g_cover p hf with h|h|h
    · exact h
    · exact False.elim (omitted h)
    · exact False.elim (owners_disjoint p hf 8 7 (by decide) _ _
        ⟨h,(northwest_pair p hf hb).2⟩)
  have marker : (owners p 8).Inside (457/500) 2 := by
    simpa [S12.marker] using marker_point p hf 8 12 (by decide +kernel)
  have markerSW : (owners p 4).Inside (33/20) (33/20) := by
    simpa [S12.marker] using marker_point p hf 4 8 (by decide +kernel)
  have tip : (owners p 8).Inside 1 (239/100) := by
    have h := local_wall_segment p mmmp hb 0 (161/100) (by norm_num) (by norm_num)
    norm_num [mmmp,wallOwner,pointMap,branchY] at h
    exact h
  let W := (pullY (pullX (owners p 8))).translated 2 2
  have wInside (x y : ℝ) : W.Inside x y ↔ (owners p 8).Inside (2-x) (2-y) := by
    simp only [W,inside_translated_iff,inside_pullY,inside_pullX]
    rw [show 4-(2+x)=2-x by ring,show 4-(2+y)=2-y by ring]
  obtain ⟨V,vc,vrange,vside,vcenter,vinside⟩ := C1092MixedWideCrossing.centered_frame W
  have actual (x y : ℝ) : V.Inside x y ↔ (owners p 8).Inside (2-x) (2-y) :=
    (vinside x y).trans (wInside x y)
  have cut : centerY V≤0 := by
    have original : 2≤centerY (owners p 8) := by
      simpa [mmmp,wallFrame,localFrame,wallOwner] using (hb 0).1
    have center : centerY W=2-centerY (owners p 8) := by
      dsimp [W,OpenSquare.translated,pullX,pullY,centerY]
      linear_combination 2*(owners p 8).unit_normal
    rw [vcenter,center]
    linarith only [original]
  have profile := C1092MixedWideWall.canonical_profile V
    (by rw [vside]; exact side_gt p 8)
    (by
      rw [vside]
      change (p.square _).side≤1001/1000
      rw [p.congruent]
      exact p.side_le) vc vrange
    (by
      intro x y own
      have h := (actual _ _).mp own
      have box := p.contained _ _ _ h
      linarith only [box.1]) cut
    (by apply (actual _ _).mpr; norm_num; exact marker)
    (by apply (actual _ _).mpr; norm_num; exact tip)
    (by apply (actual _ _).mpr; norm_num; exact lower)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact omitted h)
    (by
      intro own
      have h := (actual _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 8 4 (by decide) _ _ ⟨h,markerSW⟩)
  let B := translate (opposite V) (-1) 0
  have bInside (x y : ℝ) : B.Inside x y ↔ (owners p 8).Inside (1+x) (2+y) := by
    change (translate (opposite V) (-1) 0).Inside x y ↔ _
    rw [inside_translate,inside_opposite,actual]
    rw [show 2-(-(x+-1))=1+x by ring,show 2-(-(y+0))=2+y by ring]
  exact wide_impossible B (by dsimp [B,translate,opposite]; rw [vside]; exact side_gt p 8)
    vc profile.1 profile.2.1 profile.2.2.1
    (by apply (bInside _ _).mpr; norm_num; exact marker)
    (by apply (bInside _ _).mpr; norm_num; exact left_origin p hf hb)
    (by apply (bInside _ _).mpr; norm_num; exact tip)
    (by
      intro own
      have h := (bInside _ _).mp own
      norm_num at h
      exact owners_disjoint p hf 8 7 (by decide) _ _
        ⟨h,C1092MMMPUpperPoints.northwest_point p hf hb⟩)
    (by dsimp [B,translate,opposite]; linarith only [profile.2.2.2.2.1])
    (by
      intro x y own
      have h := (bInside _ _).mp own
      have box := p.contained _ _ _ h
      linarith only [box.1])

#print axioms point
end N12Compact.C1092MMMPLeftFar
