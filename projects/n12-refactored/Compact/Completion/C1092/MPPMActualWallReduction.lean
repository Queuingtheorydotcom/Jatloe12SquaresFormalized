import Compact.Completion.C1092.MPPMActualTwoFifths
import Compact.Completion.C1092.MPPMCentralCover

/-! Complete original-wall entrance to the remaining MPPM central
problem. A simultaneous quarter turn transports every actual square and
the four closed windmill center signs. Thus each literal ordinary wall
auxiliary is strict, including the complement of every face-contact
alternative. This module does not assert a central inward ending.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMActualWallReduction
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
open C1092MPPMOmissions C1092MPPMCentralCover
set_option Elab.async false
noncomputable section

theorem bottom_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : (owners p 9).Inside (8/5) 1 := by
  apply Classical.byContradiction
  exact C1092MPPMActualTwoFifths.impossible p hf hb

theorem right_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : (owners p 10).Inside 3 (8/5) := by
  let g : Transform := ⟨true,true,false⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have h := bottom_ordinary (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 9] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at h
  exact h

theorem top_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : (owners p 11).Inside (12/5) 3 := by
  let g : Transform := ⟨false,true,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have h := bottom_ordinary (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 9] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullX,inside_pullY] at h
  exact h

theorem left_ordinary (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : (owners p 8).Inside 1 (12/5) := by
  let g : Transform := ⟨true,false,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have h := bottom_ordinary (g.pullPacking p) (family_transport g p hf) context
  rw [owners_transport g p hf 9] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY] at h
  exact h

theorem no_missing (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) : ∀ k,¬Missing p k := by
  intro k
  fin_cases k
  · exact fun absent => absent (left_ordinary p hf hb)
  · exact fun absent => absent (bottom_ordinary p hf hb)
  · exact fun absent => absent (right_ordinary p hf hb)
  · exact fun absent => absent (top_ordinary p hf hb)

theorem wall_pairs (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) :
    ((owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5)) ∧
    ((owners p 9).Inside (8/5) 1 ∧ (owners p 9).Inside (87/50) 1) ∧
    ((owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5)) ∧
    ((owners p 11).Inside (12/5) 3 ∧ (owners p 11).Inside (113/50) 3) :=
  ordinary_walls p hb (no_missing p hf hb)

theorem southwest_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) :
    Ordinary (owners p 4) ∨ Inward (owners p 4) ∨ Elbow (owners p 4) :=
  no_omission_cover p hf hb (no_missing p hf hb)

end
#print axioms no_missing
#print axioms wall_pairs
#print axioms southwest_cover
end N12Compact.C1092MPPMActualWallReduction
