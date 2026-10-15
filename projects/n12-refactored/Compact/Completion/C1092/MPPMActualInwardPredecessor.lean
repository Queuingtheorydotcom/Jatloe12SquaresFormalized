import Compact.Completion.C1092.MPPMActualInwardMissing
import Compact.Completion.C1092.MPPMActualInwardSuccessor
import Compact.Completion.C1092.MPPMInwardFinalMissing
import Compact.Completion.C1092.MPPMInwardFinalRightBar
import Compact.Completion.C1092.RigidCharts

/-! Actual opposite-inward producers for the two OIOI endings. The
half-turn acts on the complete original packing; the resulting W is
the original Q7, with the same side and strict interior. Its sharpened
upper face comes from the real Q11 origin, not an assumed support cap.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualInward
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMCentralCover C1092MPPMInwardFinal C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

private theorem successor_origin_floor (E : OpenSquare) (side : 1<E.side)
    (h : NegativeSuccessor E) (missing : ¬E.Inside 0 (-1)) : -E.c≤E.loV := by
  have eb := normal_bounds h.normal
  have ep : 0<E.c := by linarith only [eb.1]
  have negative : E.s<0 := by
    linarith only [h.lowerV,h.upperV,side,eb.2.1,h.normal.1]
  have lowU : E.loU< -E.s := by linarith only [h.upperU,side,eb.2.1]
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [h.outer.2.1,h.outer.2.2.2,lowU,low,ep,negative]

/-- The opposite Q6 inward pair, its own G9 and its literal center
omission produce the complete negative predecessor profile of Q7. -/
theorem opposite_predecessor (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm)
    (inward : (owners p 6).Inside 2 (113/50) ∧ (owners p 6).Inside (113/50) 2)
    (nonordinary : ¬((owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5)))
    (outer : (owners p 6).Inside 3 (12/5)) (missing : ¬(owners p 6).Inside 2 2)
    (C : OpenSquare) (c : Frame p 4 C) :
    ∃ W : OpenSquare,Frame p 7 W ∧ MissingPredecessor C W := by
  let g : Transform := ⟨false,true,true⟩
  let p' := g.pullPacking p
  have family' := family_transport g p hf
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have inward' : Inward (owners p' 4) := by
    rw [owners_transport g p hf 4]
    norm_num [Inward,g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullX,inside_pullY]
    exact inward
  have nonordinary' : ¬Ordinary (owners p' 4) := by
    rw [owners_transport g p hf 4]
    norm_num [Ordinary,g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullX,inside_pullY]
    exact nonordinary
  have outer' : (owners p' 4).Inside 1 (8/5) := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullX,inside_pullY]
    exact outer
  have missing' : ¬(owners p' 4).Inside 2 2 := by
    rw [owners_transport g p hf 4]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,inside_pullX,inside_pullY]
    exact missing
  obtain ⟨N,n,np,ncanonical⟩ := canonical_frame p' 4
  have north := outer_owned p' family' context inward' nonordinary' outer' missing' N n ncanonical
  obtain ⟨F,f,fp,fcanonical⟩ := canonical_frame p' 5
  have successor := (successor_profile p' family' context inward' nonordinary'
    N F n f north.1.normal fcanonical).2
  have origin : ¬F.Inside 0 (-1) := by
    rw [f.actual]; norm_num
    exact fun own => owners_disjoint p' family' 5 9 (by decide) _ _ ⟨own,north.2.2.2⟩
  have floor := successor_origin_floor F (by rw [f.side]; exact side_gt p' 5) successor origin
  let W := C1092RigidCharts.opposite F
  have w : Frame p 7 W := by
    refine ⟨?_,?_⟩
    · change F.side=(owners p 7).side
      rw [f.side,owners_transport g p hf 5]
      rfl
    · intro x y
      rw [C1092RigidCharts.inside_opposite,f.actual,owners_transport g p hf 5]
      simp only [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
        inside_pullX,inside_pullY]
      congr 2 <;> ring
  have wm : (owners p 7).Inside (33/20) (47/20) := by
    simpa [marker] using marker_owned p hf 7 11 (by decide +kernel)
  refine ⟨W,w,?_⟩
  refine
    { same := c.side.trans ((side_same p 4 7).trans w.side.symm)
      normal := successor.normal
      marker := by rw [w.actual]; norm_num; exact wm
      lowerU := ?_
      lowerV := ?_
      upperV := ?_
      apart := Frame.apart hf c w (by decide) }
  · change -F.c+F.s≤-F.loU-F.side
    linarith only [successor.upperU]
  · change (2/5)*F.c+F.s≤-F.loV-F.side
    linarith only [successor.upperV]
  · change -F.loV-F.side+F.side≤F.c
    linarith only [floor]

/-- This shorter reach uses only the opposite inward owner's genuine
G9 and G6; no F9 or ordinary-opposite assumption is substituted. -/
theorem inward_right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (outer : (owners p 6).Inside 3 (12/5))
    (inner : (owners p 6).Inside (113/50) 2) :
    ∀ y : ℝ,-36/85≤y → y≤0 → (chart p 10).Inside 1 y := by
  have rm : (owners p 10).Inside (1543/500) 2 := by
    simpa [marker] using marker_owned p hf 10 14 (by decide +kernel)
  exact C1092MPPMInwardFinal.right_bar (owners p 10) (owners p 6) (side_gt p 10)
    (fun x y own => (p.contained _ _ _ own).2.1) rm
    (C1092MPPMActualWallReduction.wall_pairs p hf hb).2.2.1.2
    (right_origin p hf hb inward) outer inner (owners_disjoint p hf 10 6 (by decide))

theorem inward_bottom_long_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (inward : Inward (owners p 4))
    (origin : (owners p 9).Inside 2 1) :
    ∀ x : ℝ,-14/25≤x → x≤0 → (chart p 9).Inside x (-1) := by
  have far := C1092MPPMInwardNeighbors.bottom_far p hf hb
    (C1092MPPMActualWallReduction.no_missing p hf hb) inward
  intro x low high
  let t := (25/14)*(x+14/25)
  have point := inside_segment (owners p 9) (36/25) 1 2 1 t far origin
    (by dsimp [t]; linarith only [low]) (by dsimp [t]; linarith only [high])
  rw [(chart_frame p 9).actual]
  norm_num
  convert point using 1 <;> dsimp [t] <;> ring

end
#print axioms opposite_predecessor
#print axioms inward_right_bar
#print axioms inward_bottom_long_bar
end N12Compact.C1092MPPMActualInward
