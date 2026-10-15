import Compact.Completion.C1092.MMMMStrictCore
import Compact.Completion.C1092.OrdinaryHalfpoint
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! Four actual MMMM wall origins. Each transfer uses its original corner
neighbor, both true walls of that corner, and a halfpoint in a named foreign
central or wall owner. The same packing is transported in the swapped joins. -/
namespace N12Compact.C1092MMMMWalls
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092ActualEntrance C1092MMMMEntrance
open N12Compact.Completion.OtherCases.WallProfile
set_option Elab.async false

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1 < (owners p i).side := by
  change 1 < (p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side := by
  change (p.square _).side=(p.square _).side
  rw [p.congruent,p.congruent]

theorem top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 11).Inside 2 3 := by
  let B := pullY (pullX (owners p 11))
  let K := pullY (pullX (owners p 2))
  have boxB : InsideContainer B := container_pullY _ (container_pullX _ (p.contained _))
  have boxK : InsideContainer K := container_pullY _ (container_pullX _ (p.contained _))
  have markerB : (owners p 11).Inside 2 (1543/500) := by
    have h : Owns (owners p 11) 15 := (owners_markers p hf 11 15).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have markerK : (owners p 2).Inside 3 (1543/500) := by
    have h : Owns (owners p 2) 4 := (owners_markers p hf 2 4).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have corner : (owners p 2).Inside 3 3 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 2
  have strictB : B.Inside 2 (457/500) := by
    norm_num [B,inside_pullY,inside_pullX]
    exact markerB
  have auxiliaryB : B.Inside (8/5) 1 := by
    norm_num [B,inside_pullY,inside_pullX]
    exact top_f p hf hb
  have strictK : K.Inside 1 (457/500) := by
    norm_num [K,inside_pullY,inside_pullX]
    exact markerK
  have cornerK : K.Inside 1 1 := by
    norm_num [K,inside_pullY,inside_pullX]
    exact corner
  have missingK : ¬ K.Inside 1 (3/2) := by
    norm_num [K,inside_pullY,inside_pullX]
    intro h
    exact owners_disjoint p hf 2 10 (by decide) _ _
      ⟨h,C1092MMMMStrictCore.right_halfpoint p hf hb⟩
  have apart : ∀ x y, ¬ (K.Inside x y ∧ B.Inside x y) := by
    intro x y h
    have first := (inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp h.1)
    have last := (inside_pullX _ _ _).mp ((inside_pullY _ _ _).mp h.2)
    exact owners_disjoint p hf 2 11 (by decide) _ _ ⟨first,last⟩
  have h := boundary_origin B K (457/500) (8/5) (side_gt p 11) (side_same p 11 2)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    strictB auxiliaryB strictK cornerK missingK apart
  norm_num [B,inside_pullY,inside_pullX] at h
  exact h

theorem right_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 10).Inside 3 2 := by
  let g : Transform := ⟨true,false,false⟩
  have action : branchAction g mmmm=mmmm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mmmm hb
  rw [action] at context
  have h := top_origin (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 11] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap] at h
  exact h

theorem southeast_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 5).Inside 3 (3/2) := by
  have ordinary := southeast_pair p hf hb
  have inward := northeast_pair p hf mmmm hb rfl rfl
  have marker : (owners p 5).Inside (47/20) (33/20) := by
    have h : Owns (owners p 5) 9 := (owners_markers p hf 5 9).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  exact C1092OrdinaryHalfpoint.point (owners p 5) (side_gt p 5) marker ordinary.1 ordinary.2
    (fun h => owners_disjoint p hf 5 6 (by decide) _ _ ⟨h,inward.2⟩)
    (fun h => owners_disjoint p hf 5 10 (by decide) _ _ ⟨h,right_origin p hf hb⟩)
    (fun h => owners_disjoint p hf 5 1 (by decide) _ _ ⟨h,corner⟩)
    (fun h => owners_disjoint p hf 5 9 (by decide) _ _
      ⟨h,(southwest_high_wall_points p hb).2⟩)

theorem northwest_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 7).Inside (3/2) 3 := by
  let g : Transform := ⟨true,false,false⟩
  have action : branchAction g mmmm=mmmm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mmmm hb
  rw [action] at context
  have h := southeast_halfpoint (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 5] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap] at h
  exact h

theorem bottom_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 9).Inside 2 1 := by
  let B := pullX (owners p 9)
  let K := pullX (owners p 1)
  have boxB : InsideContainer B := container_pullX _ (p.contained _)
  have boxK : InsideContainer K := container_pullX _ (p.contained _)
  have markerB : (owners p 9).Inside 2 (457/500) := by
    have h : Owns (owners p 9) 13 := (owners_markers p hf 9 13).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have markerK : (owners p 1).Inside 3 (457/500) := by
    have h : Owns (owners p 1) 2 := (owners_markers p hf 1 2).mpr (by decide +kernel)
    simpa [Owns,S12.marker] using h
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have strictB : B.Inside 2 (457/500) := by norm_num [B,inside_pullX]; exact markerB
  have auxiliaryB : B.Inside (87/50) 1 := by
    norm_num [B,inside_pullX]
    exact (southwest_high_wall_points p hb).2
  have strictK : K.Inside 1 (457/500) := by norm_num [K,inside_pullX]; exact markerK
  have cornerK : K.Inside 1 1 := by norm_num [K,inside_pullX]; exact corner
  have missingK : ¬ K.Inside 1 (3/2) := by
    norm_num [K,inside_pullX]
    intro h
    exact owners_disjoint p hf 1 5 (by decide) _ _ ⟨h,southeast_halfpoint p hf hb⟩
  have apart : ∀ x y, ¬ (K.Inside x y ∧ B.Inside x y) := by
    intro x y h
    exact owners_disjoint p hf 1 9 (by decide) _ _
      ⟨(inside_pullX _ _ _).mp h.1,(inside_pullX _ _ _).mp h.2⟩
  have h := boundary_origin B K (457/500) (87/50) (side_gt p 9) (side_same p 9 1)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    strictB auxiliaryB strictK cornerK missingK apart
  norm_num [B,inside_pullX] at h
  exact h

theorem left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mmmm) : (owners p 8).Inside 1 2 := by
  let g : Transform := ⟨true,false,false⟩
  have action : branchAction g mmmm=mmmm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mmmm hb
  rw [action] at context
  have h := bottom_origin (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 9] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullSwap] at h
  exact h

#print axioms top_origin
#print axioms bottom_origin
end N12Compact.C1092MMMMWalls
