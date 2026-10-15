import Compact.Completion.C1092.MPPMPointCore
import Compact.Completion.C1092.MPPMTopOrigin
import Compact.Completion.C1092.MPPMOmissions
import Compact.Completion.C1092.MMMP.NortheastSign
import Compact.Completion.C1092.MMMP.EndingAxes
import Compact.Completion.OtherCases.TopOnlyLeftPoint

/-! The actual northeast sign and initial four-face table in the normalized
MPPM one-omission entrance. All coordinates are in the single transposed
chart; no MMMP wall-center assumption is transported to this packing. -/
namespace N12Compact.C1092MPPMUpperSign
open S12 S12Pilot C1092WallCycle C1092MPPMEntrance C1092RigidCharts
open C1092MMMPEndingAxes C977CornerCubic
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

private theorem marker_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

structure PositiveActual (p : NormalizedPacking) (N : OpenSquare) : Prop where
  side : N.side=(owners p 6).side
  actual : ∀ x y, N.Inside x y ↔ (owners p 6).Inside (2+y) (2+x)
  normal : Normal N.c N.s
  positive : 0<N.s

theorem exists_positive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1) :
    ∃ N : OpenSquare, PositiveActual p N := by
  classical
  let q := translate (pullSwap (owners p 6)) 2 2
  obtain ⟨N,nc,ns,nside,ninside,_⟩ := ClosedFrames.canonical_frame q
  let C := clockwise (translate (pullSwap (owners p 5)) 2 2)
  let B := clockwise N
  have Cin (x y : ℝ) : C.Inside x y ↔ (owners p 5).Inside (2-x) (2+y) := by
    rw [C,inside_clockwise,inside_translate,inside_pullSwap]
    rw [show -x+2=2-x by ring,show y+2=2+y by ring]
  have Bin (x y : ℝ) : B.Inside x y ↔ (owners p 6).Inside (2-x) (2+y) := by
    rw [B,inside_clockwise,ninside,q,inside_translate,inside_pullSwap]
    rw [show -x+2=2-x by ring,show y+2=2+y by ring]
  have core := C1092MPPMPointCore.rectangle p hf hb omitted
  have m5 : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  have m4 : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using marker_point p hf 4 8 (by decide +kernel)
  have m6 : (owners p 6).Inside (47/20) (47/20) := by
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have rightMarker : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_point p hf 10 14 (by decide +kernel)
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have topTip : (owners p 11).Inside (239/100) 3 := by
    have h := local_wall_segment p mppm hb 3 (161/100) (by norm_num) (by norm_num)
    norm_num [mppm,wallOwner,pointMap,branchY] at h
    exact h
  have bottomTip := omitted_bottom_bar p hf hb omitted (239/100)
    (by norm_num) (by norm_num)
  have pair := (omitted_bottom_neighbors p hf hb omitted).1
  have same : C.side=B.side := by
    change (owners p 5).side=N.side
    exact (side_same p 5 6).trans nside.symm
  have positive := C1092MMMPNortheastSign.positive C B (side_gt p 5) same nc ns
    (by apply (Cin _ _).mpr; norm_num; exact core 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by apply (Cin _ _).mpr; norm_num; exact core (5/2) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by apply (Cin _ _).mpr; norm_num; exact core 2 (3/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (by apply (Cin _ _).mpr; norm_num; exact m5)
    (by
      intro own
      have own' := (Cin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 5 4 (by decide) _ _ ⟨own',m4⟩)
    (by
      intro own
      have own' := (Cin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨own',m6⟩)
    (by
      intro own
      have own' := (Cin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨own',bottomTip⟩)
    (by apply (Bin _ _).mpr; norm_num; exact m6)
    (by apply (Bin _ _).mpr; norm_num; exact pair.1)
    (by apply (Bin _ _).mpr; norm_num; exact pair.2)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 5 (by decide) _ _
        ⟨own',core (239/100) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨own',topTip⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 10 (by decide) _ _ ⟨own',rightMarker⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨own',corner⟩)
    (by
      intro own
      have own' := (Bin _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 6 5 (by decide) _ _
        ⟨own',core (5/2) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩)
    (by
      intro x y own
      exact owners_disjoint p hf 5 6 (by decide) _ _ ⟨(Cin _ _).mp own.1,(Bin _ _).mp own.2⟩)
  have pos : 0<N.s := positive
  refine ⟨N,nside,?_,⟨pos.le,?_,N.unit_normal⟩,pos⟩
  · intro x y
    rw [ninside,q,inside_translate,inside_pullSwap]
    rw [show y+2=2+y by ring,show x+2=2+x by ring]
  · simpa only [abs_of_pos pos] using ns

structure Faces (N : OpenSquare) : Prop where
  lowerU : (2/5)*N.s≤N.loU
  lowerV : (2/5)*N.c-N.s≤N.loV
  upperU : N.loU+N.side≤N.c+N.s
  upperV : N.loV+N.side≤N.c
  angle : (1+N.c)/4<N.s

theorem faces (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 9).Inside (8/5) 1)
    (N : OpenSquare) (hN : PositiveActual p N) : Faces N := by
  classical
  have side : 1<N.side := by rw [hN.side]; exact side_gt p 6
  have cb := normal_bounds hN.normal
  have cp : 0<N.c := by linarith only [cb.1]
  have core := C1092MPPMPointCore.rectangle p hf hb omitted
  have pair := (omitted_bottom_neighbors p hf hb omitted).1
  have mark : N.Inside (7/20) (7/20) := by
    apply (hN.actual _ _).mpr
    norm_num
    simpa [marker] using marker_point p hf 6 10 (by decide +kernel)
  have top : N.Inside (13/50) 1 := by apply (hN.actual _ _).mpr; norm_num; exact pair.1
  have topF : (owners p 11).Inside (12/5) 3 := by
    by_contra absent
    have different := C1092MPPMOmissions.at_most_one p hf hb 1 3 omitted absent
    exact (by decide : (1:Fin 4)≠3) different
  have missingL : ¬N.Inside 0 (13/50) := by
    intro own
    have own' := (hN.actual _ _).mp own
    norm_num at own'
    exact owners_disjoint p hf 6 5 (by decide) _ _
      ⟨own',core (113/50) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  have missingP : ¬N.Inside 0 1 := by
    intro own
    have own' := (hN.actual _ _).mp own
    norm_num at own'
    exact owners_disjoint p hf 6 10 (by decide) _ _
      ⟨own',C1092MPPMTopOrigin.right_origin p hf hb omitted⟩
  have missingC : ¬N.Inside 1 1 := by
    intro own
    have own' := (hN.actual _ _).mp own
    norm_num at own'
    have corner : (owners p 2).Inside 3 3 := by
      simpa [cornerOwner,cornerPoint] using corner_points p hf 2
    exact owners_disjoint p hf 6 2 (by decide) _ _ ⟨own',corner⟩
  have missingB : ¬N.Inside 1 (13/50) := by
    intro own
    have own' := (hN.actual _ _).mp own
    norm_num at own'
    exact owners_disjoint p hf 6 11 (by decide) _ _
      ⟨own',(wall_auxiliaries p hb).2.2.2⟩
  have f := Completion.OtherCases.TopOnlyLeftPoint.positive_faces N side cp hN.normal.1
    hN.normal.2.1 mark top missingL missingP missingC missingB
  have lowerU : (2/5)*N.s≤N.loU := by
    apply le_of_not_gt
    intro failure
    have own : N.Inside 0 (2/5) := by
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [failure,f.2.2.2,side,mark.2.1,top.2.2.2,cp,hN.normal.1,hN.normal.2.1,cb.2.1]
    have own' := (hN.actual _ _).mp own
    norm_num at own'
    exact owners_disjoint p hf 6 5 (by decide) _ _
      ⟨own',core (12/5) 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  have lowerV : (2/5)*N.c-N.s≤N.loV := by
    apply le_of_not_gt
    intro failure
    have own : N.Inside 1 (2/5) := by
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [failure,lowerU,side,mark.1,top.2.2.2,cp,hN.normal.1,hN.normal.2.1,cb.2.1]
    have own' := (hN.actual _ _).mp own
    norm_num at own'
    exact owners_disjoint p hf 6 11 (by decide) _ _ ⟨own',topF⟩
  have span : 1<(3/5)*N.c+N.s := by linarith only [lowerV,f.2.2.2,side]
  have half := Completion.OtherCases.SharpPointScalars.half_lower N.c N.s (3/5)
    cp hN.normal.1 hN.normal.2.1 N.unit_normal span
  have ratio : 1/4<N.s/(1+N.c) := by
    dsimp [C1092WallProfileScalars.half] at half
    linarith only [half]
  have angle := (lt_div_iff₀ (by linarith only [cp] : 0<1+N.c)).mp ratio
  exact ⟨lowerU,lowerV,f.2.2.1,f.2.2.2,by linarith only [angle]⟩

#print axioms exists_positive
#print axioms faces
end N12Compact.C1092MPPMUpperSign
