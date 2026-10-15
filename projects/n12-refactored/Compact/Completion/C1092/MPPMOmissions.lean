import Compact.Completion.C1092.MPPMOmissionCenter

/-! The complete actual-wall omission split. Simultaneous whole-packing
quarter turns keep the MPPM center conditions and move the original owner
of every point. Two omitted ordinary wall auxiliaries are impossible. -/
namespace N12Compact.C1092MPPMOmissions
open S12 S12Pilot C1092WallCycle C1092WallSymmetry C1092MPPMEntrance
set_option Elab.async false
noncomputable section

def ordinaryPoint (k : Fin 4) : ℝ × ℝ :=
  ![(1,12/5),(8/5,1),(3,8/5),(12/5,3)] k

def Missing (p : NormalizedPacking) (k : Fin 4) : Prop :=
  ¬(owners p (wallOwner k)).Inside (ordinaryPoint k).1 (ordinaryPoint k).2

theorem right_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 10).Inside 3 (8/5)) :
    (owners p 6).Inside 2 2 := by
  let g : Transform := ⟨true,true,false⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have missing : ¬(owners (g.pullPacking p) 9).Inside (8/5) 1 := by
    rw [owners_transport g p hf 9]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullX]
    exact omitted
  have h := C1092MPPMOmissionCenter.bottom_center (g.pullPacking p)
    (family_transport g p hf) context missing
  rw [owners_transport g p hf 5] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullX] at h
  exact h

theorem top_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 11).Inside (12/5) 3) :
    (owners p 7).Inside 2 2 := by
  let g : Transform := ⟨false,true,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have missing : ¬(owners (g.pullPacking p) 9).Inside (8/5) 1 := by
    rw [owners_transport g p hf 9]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullX,inside_pullY]
    exact omitted
  have h := C1092MPPMOmissionCenter.bottom_center (g.pullPacking p)
    (family_transport g p hf) context missing
  rw [owners_transport g p hf 5] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullX,inside_pullY] at h
  exact h

theorem left_center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (omitted : ¬(owners p 8).Inside 1 (12/5)) :
    (owners p 4).Inside 2 2 := by
  let g : Transform := ⟨true,false,true⟩
  have action : branchAction g mppm=mppm := by funext k; fin_cases k <;> rfl
  have context := context_transport g p hf mppm hb
  rw [action] at context
  have missing : ¬(owners (g.pullPacking p) 9).Inside (8/5) 1 := by
    rw [owners_transport g p hf 9]
    norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
      inside_pullSwap,inside_pullY]
    exact omitted
  have h := C1092MPPMOmissionCenter.bottom_center (g.pullPacking p)
    (family_transport g p hf) context missing
  rw [owners_transport g p hf 5] at h
  norm_num [g,ownerAction,ownerSwap,ownerX,ownerY,Transform.pull,
    inside_pullSwap,inside_pullY] at h
  exact h

theorem center (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (k : Fin 4) (missing : Missing p k) :
    (owners p (centralOwner k)).Inside 2 2 := by
  fin_cases k
  · exact left_center p hf hb missing
  · exact C1092MPPMOmissionCenter.bottom_center p hf hb missing
  · exact right_center p hf hb missing
  · exact top_center p hf hb missing

/-- Equality/contact with an ordinary auxiliary counts as an omission.
Every two distinct such omissions give a strict common-center overlap. -/
theorem at_most_one (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (i j : Fin 4) (first : Missing p i)
    (second : Missing p j) : i=j := by
  apply Classical.byContradiction
  intro different
  have injective : ∀ i j : Fin 4, i≠j → centralOwner i≠centralOwner j := by decide +kernel
  exact owners_disjoint p hf _ _ (injective i j different) 2 2
    ⟨center p hf hb i first,center p hf hb j second⟩

theorem exhaustive (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) :
    (∀ k, ¬Missing p k) ∨ ∃ k, Missing p k ∧ ∀ j, Missing p j → j=k := by
  classical
  by_cases empty : ∀ k, ¬Missing p k
  · exact Or.inl empty
  · push_neg at empty
    obtain ⟨k,missing⟩ := empty
    exact Or.inr ⟨k,missing,fun j hj => at_most_one p hf hb j k hj missing⟩

theorem ordinary_walls (p : NormalizedPacking) (hb : WallContext p mppm)
    (empty : ∀ k, ¬Missing p k) :
    ((owners p 8).Inside 1 (113/50) ∧ (owners p 8).Inside 1 (12/5)) ∧
    ((owners p 9).Inside (8/5) 1 ∧ (owners p 9).Inside (87/50) 1) ∧
    ((owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5)) ∧
    ((owners p 11).Inside (12/5) 3 ∧ (owners p 11).Inside (113/50) 3) := by
  classical
  have auxiliary := wall_auxiliaries p hb
  have own (k : Fin 4) := not_not.mp (empty k)
  exact ⟨⟨auxiliary.1,own 0⟩,⟨own 1,auxiliary.2.1⟩,
    ⟨auxiliary.2.2.1,own 2⟩,⟨own 3,auxiliary.2.2.2⟩⟩

#print axioms at_most_one
end
end N12Compact.C1092MPPMOmissions
