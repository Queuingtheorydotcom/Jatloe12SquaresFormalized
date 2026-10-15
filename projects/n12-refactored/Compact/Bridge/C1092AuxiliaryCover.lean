import Compact.Bridge.C1092WallSymmetry
import Compact.Cases.C979.EntryQueryChunks.Chunk11
import Compact.Cases.C979.EntryQueryChunks.Chunk17

/-! Original C1092 auxiliary covering consequences.

Only two already certified single-cover domains are used: the southwest
central G domain and the left-wall G domain. Their cardinality interval is
one through three, exactly as required by the original C1092 budget. Whole
packing symmetries transport their conclusions to the other owners. No
joint ownership-vector enumeration or new numerical certificate is used.

Source checkpoint: not yet elaborated; compilation is deferred until the
complete proof is assembled. These are entrance lemmas, not a case exclusion.
-/
namespace N12Compact.C1092AuxiliaryCover
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
set_option Elab.async false

/-- The geometric refutations in a direct single-cover certificate are
independent of its original host family. Only the two budget equalities
need to be checked again. -/
private theorem rebase (w : DirectSingleDomain) (oldFamily newFamily : Finset Nat)
    (k : Fin 2) (checked : w.Check oldFamily k)
    (lower : w.lower = if w.mask ∈ auxExempt k then 0 else 1)
    (upper : w.upper = (newFamily ∩ auxExempt k).card - 2 + w.lower) :
    w.Check newFamily k :=
  ⟨lower,upper,checked.2.2⟩

theorem southwest_g_domain (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    natAuxOwners p 1 (ownerIndex p (ownerCode 4)) ∈ single979_5_1.allowed := by
  apply single979_5_1.actual family 1
    (rebase single979_5_1 case979Family family 1 single979_5_1_checked
      (by decide +kernel) (by decide +kernel)) p _ hf
  exact owner_code p hf 4

theorem left_g_domain (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    natAuxOwners p 1 (ownerIndex p (ownerCode 8)) ∈ single979_8_1.allowed := by
  apply single979_8_1.actual family 1
    (rebase single979_8_1 case979Family family 1 single979_8_1_checked
      (by decide +kernel) (by decide +kernel)) p _ hf
  exact owner_code p hf 8

/-- Every southwest central owner has at least one of these three points;
additional auxiliary ownership is explicitly retained. -/
theorem southwest_g_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owners p 4).Inside 1 (8/5) ∨
    (owners p 4).Inside (87/50) 1 ∨
    (owners p 4).Inside (87/50) 2 := by
  have cover : ∀ s ∈ single979_5_1.allowed, 0 ∈ s ∨ 2 ∈ s ∨ 3 ∈ s := by
    decide +kernel
  have point (j : Nat) (bound : j < 10)
      (member : j ∈ natAuxOwners p 1 (ownerIndex p (ownerCode 4))) :
      (owners p 4).Inside ((auxPoints 1)[j]!).1 ((auxPoints 1)[j]!).2 :=
    (nat_aux_exact p 1 (ownerIndex p (ownerCode 4)) j
      (by change j ∈ List.range 10; exact List.mem_range.mpr bound)).mpr member
  rcases cover _ (southwest_g_domain p hf) with h | h | h
  · exact Or.inl (by simpa [auxPoints,gPoints] using point 0 (by decide) h)
  · exact Or.inr (Or.inl (by simpa [auxPoints,gPoints] using point 2 (by decide) h))
  · exact Or.inr (Or.inr (by simpa [auxPoints,gPoints] using point 3 (by decide) h))

theorem left_g_cover (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owners p 8).Inside 1 (8/5) ∨
    (owners p 8).Inside 1 (12/5) ∨
    (owners p 8).Inside (87/50) 2 := by
  have cover : ∀ s ∈ single979_8_1.allowed, 0 ∈ s ∨ 1 ∈ s ∨ 3 ∈ s := by
    decide +kernel
  have point (j : Nat) (bound : j < 10)
      (member : j ∈ natAuxOwners p 1 (ownerIndex p (ownerCode 8))) :
      (owners p 8).Inside ((auxPoints 1)[j]!).1 ((auxPoints 1)[j]!).2 :=
    (nat_aux_exact p 1 (ownerIndex p (ownerCode 8)) j
      (by change j ∈ List.range 10; exact List.mem_range.mpr bound)).mpr member
  rcases cover _ (left_g_domain p hf) with h | h | h
  · exact Or.inl (by simpa [auxPoints,gPoints] using point 0 (by decide) h)
  · exact Or.inr (Or.inl (by simpa [auxPoints,gPoints] using point 1 (by decide) h))
  · exact Or.inr (Or.inr (by simpa [auxPoints,gPoints] using point 3 (by decide) h))

theorem central_cover_transported (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owners p (ownerAction g 4)).Inside (g.apply 1 (8/5)).1 (g.apply 1 (8/5)).2 ∨
    (owners p (ownerAction g 4)).Inside (g.apply (87/50) 1).1 (g.apply (87/50) 1).2 ∨
    (owners p (ownerAction g 4)).Inside (g.apply (87/50) 2).1 (g.apply (87/50) 2).2 := by
  have h := southwest_g_cover (g.pullPacking p) (family_transport g p hf)
  rw [owners_transport g p hf 4] at h
  simpa only [inside_pull] using h

theorem wall_cover_transported (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    (owners p (ownerAction g 8)).Inside (g.apply 1 (8/5)).1 (g.apply 1 (8/5)).2 ∨
    (owners p (ownerAction g 8)).Inside (g.apply 1 (12/5)).1 (g.apply 1 (12/5)).2 ∨
    (owners p (ownerAction g 8)).Inside (g.apply (87/50) 2).1 (g.apply (87/50) 2).2 := by
  have h := left_g_cover (g.pullPacking p) (family_transport g p hf)
  rw [owners_transport g p hf 8] at h
  simpa only [inside_pull] using h

theorem northwest_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 7).Inside 1 (113/50) ∨
    (owners p 7).Inside (8/5) 3 ∨
    (owners p 7).Inside 2 (113/50) := by
  have h := central_cover_transported ⟨true,false,true⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem northwest_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 7).Inside 1 (12/5) ∨
    (owners p 7).Inside (87/50) 2 ∨
    (owners p 7).Inside (87/50) 3 := by
  have h := central_cover_transported ⟨false,false,true⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem northeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 6).Inside 2 (113/50) ∨
    (owners p 6).Inside (12/5) 3 ∨
    (owners p 6).Inside 3 (113/50) := by
  have h := central_cover_transported ⟨true,true,true⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem northeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 6).Inside (113/50) 2 ∨
    (owners p 6).Inside (113/50) 3 ∨
    (owners p 6).Inside 3 (12/5) := by
  have h := central_cover_transported ⟨false,true,true⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem top_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 11).Inside (8/5) 3 ∨
    (owners p 11).Inside 2 (113/50) ∨
    (owners p 11).Inside (12/5) 3 := by
  have h := wall_cover_transported ⟨true,false,true⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem right_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 10).Inside (113/50) 2 ∨
    (owners p 10).Inside 3 (8/5) ∨
    (owners p 10).Inside 3 (12/5) := by
  have h := wall_cover_transported ⟨false,true,false⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

theorem southeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p = family) :
    (owners p 5).Inside (113/50) 1 ∨
    (owners p 5).Inside (113/50) 2 ∨
    (owners p 5).Inside 3 (8/5) := by
  have h := central_cover_transported ⟨false,true,false⟩ p hf
  norm_num [Transform.apply,ownerAction,ownerSwap,ownerX,ownerY] at h
  tauto

#print axioms southwest_g_domain
#print axioms northwest_f_cover
#print axioms top_f_cover
end N12Compact.C1092AuxiliaryCover
