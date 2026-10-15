import Compact.Completion.C1092.MPPMActualWallReduction
import Compact.Completion.C1092.MPPMElbows
import Compact.Completion.C1092.MPPMInwardNeighbors
import Compact.Completion.C1092.MPPMElbowIsolation
import Compact.Completion.C1092.MPPMActualNonordinaryFar
import Compact.Completion.C1092.MPPMOrdinaryWallAdvance
import Compact.Completion.C1092.MPPMElbowSuccessor
import Compact.Completion.C1092.MPPMActualPositiveOrder

/-! Actual residual-elbow ancestry. Every no-omission premise is derived
from the completed original wall reduction. The two-elbow obstruction
compares two canonical frames of the same original Q4/Q5, transporting
the entire successor rather than selecting its points independently.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualNonordinary
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMOmissions
set_option Elab.async false
noncomputable section

private theorem side_gt (p : NormalizedPacking) (i : Fin 12) : 1<(owners p i).side := by
  change 1<(p.square _).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem side_same (p : NormalizedPacking) (i j : Fin 12) :
    (owners p i).side=(owners p j).side :=
  (p.congruent _).trans (p.congruent _).symm

private theorem mark (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (i : Fin 12) (j : Marker) (member : j∈maskSupport (ownerCode i)) :
    (owners p i).Inside (marker j).1 (marker j).2 :=
  (owners_markers p hf i j).mpr member

theorem successor_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (elbow : Elbow (owners p 4)) :
    (owners p 5).Inside (12/5) 1 ∧ (owners p 5).Inside (113/50) 1 := by
  let g : Transform := ⟨true,true,false⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have family' := family_transport g p hf
  have empty := C1092MPPMActualWallReduction.no_missing (g.pullPacking p) family' context
  rcases C1092MPPMCentralCover.no_omission_cover (g.pullPacking p) family' context empty with
      ordinary|inward|nextElbow
  · have pair := ordinary
    rw [Ordinary,owners_transport g p hf 4] at pair
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX] at pair
    exact ⟨pair.2,pair.1⟩
  · have pair := C1092MPPMInwardNeighbors.northwest_pair
      (g.pullPacking p) family' context empty inward
    rw [owners_transport g p hf 7] at pair
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX] at pair
    exact False.elim (elbow.2.2.1 pair.1)
  · obtain ⟨C,cside,cactual,cp⟩ := C1092MPPMElbows.southwest_profile p hf hb
      (C1092MPPMActualWallReduction.no_missing p hf hb) elbow
    obtain ⟨D,dside,dactual,dp⟩ := C1092MPPMElbows.southwest_profile
      (g.pullPacking p) family' context empty nextElbow
    have dshape : D.side=(owners p 5).side := by
      rw [dside,owners_transport g p hf 4]
      rfl
    have actualD (x y : ℝ) (own : D.Inside y (-x)) :
        (owners p 5).Inside (x+2) (y+2) := by
      have original := (dactual _ _).mp own
      rw [owners_transport g p hf 4] at original
      norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullSwap,inside_pullX] at original
      convert original using 1 <;> ring
    have M : (owners p 4).Inside (33/20) (33/20) := by
      simpa [marker] using mark p hf 4 8 (by decide +kernel)
    have N : (owners (g.pullPacking p) 4).Inside (33/20) (33/20) := by
      simpa [marker] using mark (g.pullPacking p) family' 4 8 (by decide +kernel)
    apply False.elim
    apply C1092MPPMElbowIsolation.impossible C D
      (by rw [cside]; exact side_gt p 4)
      (cside.trans ((side_same p 4 5).trans dshape.symm)) cp dp
    · apply (cactual _ _).mpr; norm_num; exact M
    · apply (dactual _ _).mpr; norm_num; exact N
    · apply (dactual _ _).mpr; norm_num; exact nextElbow.2.1
    · exact fun x y both => owners_disjoint p hf 4 5 (by decide) _ _
        ⟨(cactual _ _).mp both.1,actualD x y both.2⟩

theorem predecessor_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (elbow : Elbow (owners p 4)) :
    (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3 := by
  let g : Transform := ⟨true,false,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have family' := family_transport g p hf
  have empty := C1092MPPMActualWallReduction.no_missing (g.pullPacking p) family' context
  rcases C1092MPPMCentralCover.no_omission_cover (g.pullPacking p) family' context empty with
      ordinary|inward|previousElbow
  · have pair := ordinary
    rw [Ordinary,owners_transport g p hf 4] at pair
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] at pair
    exact ⟨pair.2,pair.1⟩
  · have pair := C1092MPPMInwardNeighbors.southeast_pair
      (g.pullPacking p) family' context empty inward
    rw [owners_transport g p hf 5] at pair
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] at pair
    exact False.elim (elbow.2.2.1 pair.1)
  · have pair := successor_ordinary (g.pullPacking p) family' context previousElbow
    rw [owners_transport g p hf 5] at pair
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY] at pair
    exact False.elim (elbow.2.2.1 pair.1)

/-- The ordinary missing-forward halfpoint is used in its exact rotated
Q7 chart. It does not need all four central owners to be ordinary. -/
theorem northwest_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm)
    (ordinary : (owners p 7).Inside (8/5) 3 ∧ (owners p 7).Inside (87/50) 3)
    (missing : ¬(owners p 7).Inside 2 (113/50)) : (owners p 7).Inside (3/2) 3 := by
  let g : Transform := ⟨true,false,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have P : (owners (g.pullPacking p) 4).Inside 1 (87/50) := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact ordinary.2
  have G : (owners (g.pullPacking p) 4).Inside 1 (8/5) := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact ordinary.1
  have absent : ¬(owners (g.pullPacking p) 4).Inside (87/50) 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact missing
  have point := C1092MPPMPositiveSeedsActual.missing_halfpoint
    (g.pullPacking p) (family_transport g p hf) context P G absent
  rw [owners_transport g p hf 4] at point
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY] at point
  exact point

theorem left_origin_of_halfpoint (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (half : (owners p 7).Inside (3/2) 3) : (owners p 8).Inside 1 2 := by
  apply Classical.byContradiction
  intro missing
  have foreign := C1092MPPMActualRightNear.corner_halfpoint_of_missing_left_origin
    p hf (C1092MPPMActualWallReduction.left_ordinary p hf hb) missing
  exact owners_disjoint p hf 7 3 (by decide) _ _ ⟨half,foreign⟩

/-- Both reviewed local elbow endings joined to the actual Q4/Q5/Q8.
The all-angle negative successor frame is the sole upstream producer
in this intermediate statement; no far point or origin is assumed. -/
theorem impossible_of_negative_successor (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mppm)
    (elbow : Elbow (owners p 4))
    (E : OpenSquare) (eside : E.side=(owners p 5).side)
    (eactual : ∀ x y,E.Inside x y↔(owners p 5).Inside (2+x) (2+y))
    (en : C977CornerCubic.Normal E.c (-E.s)) : False := by
  have walls := C1092MPPMActualWallReduction.wall_pairs p hf hb
  have next := successor_ordinary p hf hb elbow
  have previous := predecessor_ordinary p hf hb elbow
  obtain ⟨C,cside,cactual,profile⟩ := C1092MPPMElbows.southwest_profile p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) elbow
  have actualC (x y : ℝ) : C.Inside x y↔(owners p 4).Inside (2+x) (2+y) := by
    simpa only [add_comm] using cactual x y
  have same : C.side=E.side := cside.trans ((side_same p 4 5).trans eside.symm)
  have cm : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  have lm : (owners p 8).Inside (457/500) 2 := by
    simpa [marker] using mark p hf 8 12 (by decide +kernel)
  have M : C.Inside (-7/20) (-7/20) := by apply (actualC _ _).mpr; norm_num; exact cm
  have P : C.Inside (-1) (-13/50) := by apply (actualC _ _).mpr; norm_num; exact elbow.1
  have Q : C.Inside (-13/50) 0 := by apply (actualC _ _).mpr; norm_num; exact elbow.2.1
  have EM : E.Inside (7/20) (-7/20) := by apply (eactual _ _).mpr; norm_num; exact em
  have EA : E.Inside (13/50) (-1) := by apply (eactual _ _).mpr; norm_num; exact next.2
  have EB : E.Inside (2/5) (-1) := by apply (eactual _ _).mpr; norm_num; exact next.1
  have EG : ¬E.Inside 1 (-2/5) := by
    intro own
    have original := (eactual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨original,walls.2.2.1.2⟩
  have EK : ¬E.Inside 1 (-1) := by
    intro own
    have original := (eactual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨original,corner⟩
  have ER : ¬E.Inside 0 (-543/500) := by
    intro own
    have original := (eactual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨original,bm⟩
  have apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y) := fun x y both =>
    owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(actualC _ _).mp both.1,(eactual _ _).mp both.2⟩
  have noF9 : ¬(owners p 6).Inside 3 (113/50) := by
    intro F9
    have far := C1092MPPMOrdinaryWallAdvance.right_far p hf hb
      walls.2.2.1.2 walls.2.2.2.1 F9
    let L := (owners p 8).translated 2 2
    have actualL (x y : ℝ) : L.Inside x y↔(owners p 8).Inside (2+x) (2+y) :=
      inside_translated_iff _ _ _ _ _
    apply far_impossible C E L (by rw [cside]; exact side_gt p 4) same profile en
      M P Q EM EA EB EG EK ER
    · intro own
      have original := (eactual _ _).mp own
      norm_num at original
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨original,far⟩
    · apply (actualL _ _).mpr; norm_num; exact lm
    · apply (actualL _ _).mpr; norm_num; exact walls.1.1
    · exact apart
    · exact fun x y both => owners_disjoint p hf 4 8 (by decide) _ _
        ⟨(actualC _ _).mp both.1,(actualL _ _).mp both.2⟩
  have opposite : (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2 := by
    let g : Transform := ⟨false,true,true⟩
    have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
    have context := context_transport g p hf mppm hb
    rw [action] at context
    have family' := family_transport g p hf
    rcases C1092MPPMActualWallReduction.southwest_cover (g.pullPacking p) family' context with
        ordinary|inward|otherElbow
    · have own := ordinary.1
      rw [owners_transport g p hf 4] at own
      norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullX,inside_pullY] at own
      exact False.elim (noF9 own)
    · have pair := inward
      rw [Inward,owners_transport g p hf 4] at pair
      norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullX,inside_pullY] at pair
      exact pair
    · have own := otherElbow.1
      rw [owners_transport g p hf 4] at own
      norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullX,inside_pullY] at own
      exact False.elim (noF9 own)
  have missingNW : ¬(owners p 7).Inside 2 (113/50) := fun own =>
    owners_disjoint p hf 7 6 (by decide) _ _ ⟨own,opposite.1⟩
  have origin := left_origin_of_halfpoint p hf hb (northwest_halfpoint p hf hb previous missingNW)
  apply origin_impossible C E (by rw [cside]; exact side_gt p 4) same profile en M P Q
  · intro own
    have original := (actualC _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 4 8 (by decide) _ _ ⟨original,origin⟩
  · exact EM
  · exact EA
  · exact EB
  · exact EG
  · exact EK
  · exact ER
  · exact apart

/-- Complete actual Q4 residual-elbow exclusion. The all-angle local
successor theorem produces the negative physical frame before either
ending is applied. No successor sign, far endpoint or origin is a premise. -/
theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (elbow : Elbow (owners p 4)) : False := by
  have next := successor_ordinary p hf hb elbow
  have walls := C1092MPPMActualWallReduction.wall_pairs p hf hb
  obtain ⟨C,cside,cactual,profile⟩ := C1092MPPMElbows.southwest_profile p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) elbow
  let E := (owners p 5).translated 2 2
  have actualE (x y : ℝ) : E.Inside x y↔(owners p 5).Inside (2+x) (2+y) :=
    inside_translated_iff _ _ _ _ _
  have actualC (x y : ℝ) : C.Inside x y↔(owners p 4).Inside (2+x) (2+y) := by
    simpa only [add_comm] using cactual x y
  have cm : (owners p 4).Inside (33/20) (33/20) := by
    simpa [marker] using mark p hf 4 8 (by decide +kernel)
  have em : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using mark p hf 5 9 (by decide +kernel)
  have corner : (owners p 1).Inside 3 1 := by
    simpa [cornerOwner,cornerPoint] using corner_points p hf 1
  have bm : (owners p 9).Inside 2 (457/500) := by
    simpa [marker] using mark p hf 9 13 (by decide +kernel)
  have M : C.Inside (-7/20) (-7/20) := by apply (actualC _ _).mpr; norm_num; exact cm
  have EM : E.Inside (7/20) (-7/20) := by apply (actualE _ _).mpr; norm_num; exact em
  have EA : E.Inside (13/50) (-1) := by apply (actualE _ _).mpr; norm_num; exact next.2
  have EB : E.Inside (2/5) (-1) := by apply (actualE _ _).mpr; norm_num; exact next.1
  have EG : ¬E.Inside 1 (-2/5) := by
    intro own
    have original := (actualE _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨original,walls.2.2.1.2⟩
  have EK : ¬E.Inside 1 (-1) := by
    intro own
    have original := (actualE _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 1 (by decide) _ _ ⟨original,corner⟩
  have ER : ¬E.Inside 0 (-543/500) := by
    intro own
    have original := (actualE _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨original,bm⟩
  have apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y) := fun x y both =>
    owners_disjoint p hf 4 5 (by decide) _ _
      ⟨(actualC _ _).mp both.1,(actualE _ _).mp both.2⟩
  obtain ⟨F,fside,factual,normal,_,_⟩ := C1092MPPMElbowSuccessor.negative_successor C E
    (by rw [cside]; exact side_gt p 4) (cside.trans (side_same p 4 5))
    profile M EM EA EB EG EK ER apart
  exact impossible_of_negative_successor p hf hb elbow F fside
    (fun x y => (factual x y).trans (actualE x y)) normal

theorem ordinary_or_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : Ordinary (owners p 4) ∨ Inward (owners p 4) := by
  rcases C1092MPPMActualWallReduction.southwest_cover p hf hb with ordinary|inward|elbow
  · exact Or.inl ordinary
  · exact Or.inr inward
  · exact False.elim (impossible p hf hb elbow)

/-- Every sector is covered by its genuine ordinary or inward pair.
The two pairs may overlap. The no-elbow proof is transported as a whole. -/
theorem all_ordinary_or_inward (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (i : Fin 4) :
    Ordinary (owners ((C1092MPPMActualPositiveOrder.rotation i).pullPacking p) 4) ∨
      Inward (owners ((C1092MPPMActualPositiveOrder.rotation i).pullPacking p) 4) :=
  ordinary_or_inward _ (family_transport _ p hf)
    (C1092MPPMActualPositiveOrder.rotation_context p hf hb i)

end
#print axioms successor_ordinary
#print axioms predecessor_ordinary
#print axioms impossible_of_negative_successor
#print axioms impossible
#print axioms all_ordinary_or_inward
end N12Compact.C1092MPPMActualNonordinary
