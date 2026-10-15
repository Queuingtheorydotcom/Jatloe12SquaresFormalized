import Compact.Completion.C1092.MPPMOmissionCenter
import Compact.Completion.C1092.MixedCornerObstruction
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Completion.C981.TopReach

/-! The genuine mixed-wall/corner obstruction forces the top origin in
the transposed one-omission chart. In original coordinates it is the right
wall point (3,2), retained in its actual owner. -/
namespace N12Compact.C1092MPPMTopOrigin
open S12 S12Pilot C1092WallCycle C1092MPPMEntrance C1092RigidCharts
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_cap (p : NormalizedPacking) (i : Fin 12) :
    (owners p i).side≤1001/1000 := by
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

private def chart (q : OpenSquare) : OpenSquare := translate (pullSwap (pullY q)) 2 2

private theorem inside_chart (q : OpenSquare) (x y : ℝ) :
    (chart q).Inside x y ↔ q.Inside (2+y) (2-x) := by
  rw [chart,inside_translate,inside_pullSwap,inside_pullY]
  rw [show y+2=2+y by ring,show 4-(x+2)=2-x by ring]

private theorem center_chart (q : OpenSquare) : centerY (chart q)=centerX q-2 := by
  dsimp [chart,translate,pullSwap,pullY,centerY,centerX]
  nlinarith only [q.unit_normal]

private theorem corner_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (missing : ¬(owners p 10).Inside 3 2) : (owners p 1).Inside (5/2) 1 := by
  classical
  by_contra absent
  let B := pullSwap (pullX (owners p 10))
  let K := pullSwap (pullX (owners p 1))
  have bInside (x y : ℝ) : B.Inside x y ↔ (owners p 10).Inside (4-y) x := by
    rw [B,inside_pullSwap,inside_pullX]
  have kInside (x y : ℝ) : K.Inside x y ↔ (owners p 1).Inside (4-y) x := by
    rw [K,inside_pullSwap,inside_pullX]
  have h := Completion.OtherCases.WallProfile.boundary_origin B K (457/500) (8/5)
    (side_gt p 10) (side_same p 10 1)
    (by
      intro x y h
      have box := p.contained _ _ _ ((bInside _ _).mp h)
      linarith only [box.2.1])
    (by
      intro x y h
      have box := p.contained _ _ _ ((kInside _ _).mp h)
      exact ⟨by linarith only [box.2.2.1],by linarith only [box.2.1]⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by
      apply (bInside _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 10 14 (by decide +kernel))
    (by
      apply (bInside _ _).mpr
      norm_num
      exact (omitted_bottom_neighbors p hf hb omitted).2.2)
    (by
      apply (kInside _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 1 3 (by decide +kernel))
    (by
      apply (kInside _ _).mpr
      norm_num
      simpa [cornerOwner,cornerPoint] using corner_points p hf 1)
    (by intro h; have h' := (kInside _ _).mp h; norm_num at h'; exact absent h')
    (fun x y h => owners_disjoint p hf 1 10 (by decide) _ _
      ⟨(kInside _ _).mp h.1,(bInside _ _).mp h.2⟩)
  have actual := (bInside _ _).mp h
  norm_num at actual
  exact missing actual

private theorem right_alternative (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (missing : ¬(owners p 10).Inside 3 2) : (owners p 10).Inside 3 (6/5) := by
  let T := translate (pullSwap (pullY (owners p 10))) 2 3
  have actual (x y : ℝ) : T.Inside x y ↔ (owners p 10).Inside (3+y) (2-x) := by
    rw [T,inside_translate,inside_pullSwap,inside_pullY]
    rw [show y+3=3+y by ring,show 4-(x+2)=2-x by ring]
  have h := C981CompletionTopReach.origin_alternative T (side_gt p 10)
    (by
      intro x y h
      have box := p.contained _ _ _ ((actual _ _).mp h)
      linarith only [box.2.1])
    (by
      apply (actual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 10 14 (by decide +kernel))
    (by
      apply (actual _ _).mpr
      norm_num
      exact (omitted_bottom_neighbors p hf hb omitted).2.2)
    (by intro h; have h' := (actual _ _).mp h; norm_num at h'; exact missing h')
  have result := (actual _ _).mp h
  norm_num at result
  exact result

theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    (owners p 10).Inside 3 2 := by
  classical
  by_contra missing
  have half := corner_halfpoint p hf hb omitted missing
  have alternative := right_alternative p hf hb omitted missing
  have bar := omitted_bottom_bar p hf hb omitted
  let W := chart (owners p 9)
  obtain ⟨V,vc,range,vside,vcenter,vinside⟩ := C1092MixedWideCrossing.centered_frame W
  have vActual (x y : ℝ) : V.Inside x y ↔ (owners p 9).Inside (2+y) (2-x) :=
    (vinside x y).trans (inside_chart _ x y)
  have sideV : 1<V.side := by rw [vside]; exact side_gt p 9
  have capV : V.side≤1001/1000 := by rw [vside]; exact side_cap p 9
  have wallV : ∀ x y, V.Inside x y → x≤2 := by
    intro x y h
    have box := p.contained _ _ _ ((vActual _ _).mp h)
    linarith only [box.2.2.1]
  have cutV : centerY V≤0 := by
    rw [vcenter]
    change centerY (chart (owners p 9))≤0
    rw [center_chart]
    have original : centerX (owners p 9)≤2 := by
      simpa [mppm,wallFrame,localFrame,wallOwner] using (hb 1).1
    linarith only [original]
  have profile := C1092MixedWideWall.canonical_profile V sideV capV vc range wallV cutV
    (by
      apply (vActual _ _).mpr
      norm_num
      simpa [marker] using marker_point p hf 9 13 (by decide +kernel))
    (by apply (vActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
    (by apply (vActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
    (by intro h; have h' := (vActual _ _).mp h; norm_num at h'; exact omitted h')
    (by
      intro h
      have h' := (vActual _ _).mp h
      norm_num at h'
      have foreign : (owners p 5).Inside (47/20) (33/20) := by
        simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
      exact owners_disjoint p hf 9 5 (by decide) _ _ ⟨h',foreign⟩)
  let L := translate (turnFrame (turnFrame (pullX V))) 3 0
  let K := translate (pullSwap (owners p 1)) 1 2
  have lActual (x y : ℝ) : L.Inside x y ↔ (owners p 9).Inside (2+y) (1+x) := by
    rw [L,inside_translate,turnFrame_inside,turnFrame_inside,inside_pullX,vActual]
    rw [show 2+(y+0)=2+y by ring,show 2-(4-(x+3))=1+x by ring]
  have kActual (x y : ℝ) : K.Inside x y ↔ (owners p 1).Inside (2+y) (1+x) := by
    rw [K,inside_translate,inside_pullSwap]
    rw [show y+2=2+y by ring,show x+1=1+x by ring]
  have normalL : C977CornerCubic.Normal L.c L.s := by
    refine ⟨?_,?_,L.unit_normal⟩
    · dsimp [L,translate,turnFrame,pullX]
      linarith only [profile.1]
    · dsimp [L,translate,turnFrame,pullX]
      linarith only [profile.2.1]
  have sineL : 0<L.s := by
    dsimp [L,translate,turnFrame,pullX]
    linarith only [profile.1]
  have faceL : -(2/5)*L.c≤L.loV := by
    dsimp [L,translate,turnFrame,pullX]
    linarith only [profile.2.2.2.2.1]
  exact C1092MixedCornerObstruction.impossible L K sideV
    (vside.trans (side_same p 9 1)) normalL sineL
    (by apply (lActual _ _).mpr; norm_num; exact bar _ (by norm_num) (by norm_num))
    faceL
    (by apply (kActual _ _).mpr; norm_num; exact half)
    (by
      apply (kActual _ _).mpr
      norm_num
      simpa [cornerOwner,cornerPoint] using corner_points p hf 1)
    (by
      intro h
      have h' := (kActual _ _).mp h
      norm_num at h'
      exact owners_disjoint p hf 1 10 (by decide) _ _ ⟨h',alternative⟩)
    (fun x y h => owners_disjoint p hf 9 1 (by decide) _ _
      ⟨(lActual _ _).mp h.1,(kActual _ _).mp h.2⟩)

theorem right_segment (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (y : ℝ) (low : 36/25≤y) (high : y≤2) : (owners p 10).Inside 3 y :=
  CommonCases.OriginalOwners.vertical_segment (owners p 10) 3 (36/25) 2 y
    (C1092MPPMOmissionCenter.right_far p hf hb omitted) (right_origin p hf hb omitted)
    (by norm_num) low high

#print axioms right_origin
#print axioms right_segment
end N12Compact.C1092MPPMTopOrigin
