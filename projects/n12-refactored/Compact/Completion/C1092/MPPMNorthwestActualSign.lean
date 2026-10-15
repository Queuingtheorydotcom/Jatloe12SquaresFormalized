import Compact.Completion.C1092.MPPMNorthwestSign
import Compact.Completion.C1092.MixedWideWall

/-! The complete local northwest sign argument joined to the original
one-omission owners. The actual bottom center cut becomes the mixed-left
center inequality and is never replaced by the MMMP cut. -/
namespace N12Compact.C1092MPPMNorthwestActualSign
open S12 S12Pilot C1092WallCycle C1092MPPMEntrance C1092RigidCharts C977CornerCubic
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_cap (p : NormalizedPacking) (i : Fin 12) : (owners p i).side≤1001/1000 := by
  change (p.square _).side≤1001/1000
  rw [p.congruent]
  exact p.side_le

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

structure PositiveActual (p : NormalizedPacking) (W : OpenSquare) : Prop where
  side : W.side=(owners p 5).side
  actual : ∀ x y, W.Inside x y ↔ (owners p 5).Inside (2+y) (2+x)
  normal : Normal W.c W.s
  positive : 0<W.s

theorem exists_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    ∃ W : OpenSquare, PositiveActual p W := by
  classical
  obtain ⟨N,hN⟩ := C1092MPPMUpperSign.exists_positive p hf hb omitted
  have nf := C1092MPPMUpperSign.faces p hf hb omitted N hN
  let q := translate (pullSwap (owners p 5)) 2 2
  obtain ⟨W,wc,ws,wside,winside,_⟩ := ClosedFrames.canonical_frame q
  have wActual (x y : ℝ) : W.Inside x y ↔ (owners p 5).Inside (2+y) (2+x) := by
    rw [winside,q,inside_translate,inside_pullSwap]
    rw [show y+2=2+y by ring,show x+2=2+x by ring]
  let B := translate (pullSwap (pullY (owners p 9))) 2 2
  have bActual (x y : ℝ) : B.Inside x y ↔ (owners p 9).Inside (2+y) (2-x) := by
    rw [B,inside_translate,inside_pullSwap,inside_pullY]
    rw [show y+2=2+y by ring,show 4-(x+2)=2-x by ring]
  have bCenter : centerY B=centerX (owners p 9)-2 := by
    dsimp [B,translate,pullSwap,pullY,centerY,centerX]
    linear_combination -2*(owners p 9).unit_normal
  obtain ⟨V,vc,vs,vside,vcenter,vinside⟩ := C1092MixedWideCrossing.centered_frame B
  have vActual (x y : ℝ) : V.Inside x y ↔ (owners p 9).Inside (2+y) (2-x) :=
    (vinside _ _).trans (bActual _ _)
  have sideV : 1<V.side := by rw [vside]; exact side_gt p 9
  have capV : V.side≤1001/1000 := by rw [vside]; exact side_cap p 9
  have cutV : centerY V≤0 := by
    rw [vcenter,bCenter]
    have cut : centerX (owners p 9)≤2 := by
      simpa [mppm,wallFrame,localFrame,wallOwner] using (hb 1).1
    linarith only [cut]
  have bar := omitted_bottom_bar p hf hb omitted
  have m5 : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have m4 : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have m6 : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have profile := C1092MixedWideWall.canonical_profile V sideV capV vc vs
    (by
      intro x y own
      have box := p.contained _ _ _ ((vActual _ _).mp own)
      linarith only [box.2.2.1]) cutV
    (by
      apply (vActual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 9 13 (by decide +kernel))
    (by apply (vActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
    (by apply (vActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
    (by intro own; have own' := (vActual _ _).mp own; norm_num at own'; exact omitted own')
    (by
      intro own
      have own' := (vActual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 9 5 (by decide) _ _ ⟨own',m5⟩)
  let L := turnFrame (turnFrame (translate (pullX V) 4 0))
  have lActual (x y : ℝ) : L.Inside x y ↔ (owners p 9).Inside (2+y) (2+x) := by
    rw [L,turnFrame_inside,turnFrame_inside,inside_translate,inside_pullX,vActual]
    rw [show 2+(y+0)=2+y by ring,show 2-(4-(x+4))=2+x by ring]
  have ln : Normal L.c L.s := by
    refine ⟨?_,?_,L.unit_normal⟩
    · dsimp [L,turnFrame,translate,pullX]
      linarith only [profile.1]
    · dsimp [L,turnFrame,translate,pullX]
      linarith only [profile.2.1]
  have sumL : 5/4<L.c+L.s := by
    dsimp [L,turnFrame,translate,pullX]
    exact profile.2.2.1
  have centerL : centerY L≤0 := by
    have equality : centerY L=centerY V := by
      dsimp [L,turnFrame,translate,pullX,centerY]
      ring
    rw [equality]
    exact cutV
  have positive : 0<W.s := by
    apply lt_of_not_ge
    intro sign
    have dn : Normal W.c (-W.s) := ⟨by linarith only [sign],
      by simpa only [abs_of_nonpos sign] using ws,by nlinarith only [W.unit_normal]⟩
    exact C1092MPPMNorthwestSign.nonpositive_impossible W N L
      (by rw [wside]; exact side_gt p 5)
      (wside.trans ((side_same p 5 6).trans hN.side.symm))
      (wside.trans ((side_same p 5 9).trans vside.symm)) dn hN.normal hN.positive nf
      (by apply (wActual _ _).mpr; norm_num; exact C1092MPPMOmissionCenter.bottom_center p hf hb omitted)
      (by apply (wActual _ _).mpr; norm_num; exact C1092MPPMPointCore.bottom_crosspoint p hf hb omitted)
      (by apply (wActual _ _).mpr; norm_num; exact (C1092MPPMPointCore.diagonal p hf hb omitted).1)
      (by apply (wActual _ _).mpr; norm_num; exact m5)
      (by
        intro own
        have own' := (wActual _ _).mp own
        norm_num at own'
        exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨own',m4⟩)
      (by
        intro own
        have own' := (wActual _ _).mp own
        norm_num at own'
        exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨own',m6⟩)
      (by apply (hN.actual _ _).mpr; norm_num; exact m6)
      (by apply (hN.actual _ _).mpr; norm_num; exact (omitted_bottom_neighbors p hf hb omitted).1.2)
      ln sumL centerL
      (by apply (lActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
      (by apply (lActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
      (by apply (lActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
      (fun x y own => owners_disjoint p hf 5 6 (by decide) _ _
        ⟨(wActual _ _).mp own.1,(hN.actual _ _).mp own.2⟩)
      (fun x y own => owners_disjoint p hf 5 9 (by decide) _ _
        ⟨(wActual _ _).mp own.1,(lActual _ _).mp own.2⟩)
  refine ⟨W,wside,wActual,⟨positive.le,?_,W.unit_normal⟩,positive⟩
  simpa only [abs_of_pos positive] using ws

#print axioms exists_positive
end N12Compact.C1092MPPMNorthwestActualSign
