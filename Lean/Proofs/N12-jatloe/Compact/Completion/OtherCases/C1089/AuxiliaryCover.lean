import Compact.Completion.CommonCases.DirectSingleBudget
import Compact.Completion.OtherCases.C1089.OriginalData
import Compact.Cases.C979.EntryQueryChunks.Chunk11
import Compact.Cases.C979.EntryQueryChunks.Chunk17

/-! Direct reuse of the existing central-G and wall-G certificates on
the actual C1089 packing. Its F/G budget is 1..2 for each ordinary owner,
contained in the checked 1..3 interval. The complete owned set is pulled
through an exact ten-point permutation; the family is never replaced by
C979 or C1092. Source only; no new certificate or compiler run. -/
namespace N12Compact.Completion.OtherCases.C1089.AuxiliaryCover
open S12 S12Pilot OriginalData
set_option Elab.async false
noncomputable section

theorem exemption_count (k : Fin 2) : (family∩auxExempt k).card=3 := by
  fin_cases k <;> decide +kernel

private theorem mask_member (i : Fin 12) : masks i∈family := by
  have all : ∀ j : Fin 12,masks j∈family := by decide +kernel
  exact all i

/-- A single reusable actual-owner transport. The host family supplies
only the checked local refutations. The actual cardinality comes from
C1089, and the actual markers are transported with the same physical square. -/
theorem transported_cover (w : DirectSingleDomain) (checked : w.Check case979Family 1)
    (candidate : w.mask∈candidateMasks) (lower : w.lower≤1) (upper : 2≤w.upper)
    (a b c : Fin 10)
    (cover : ∀ s∈w.allowed,a.val∈s ∨ b.val∈s ∨ c.val∈s)
    (t : Transform) (transform : t∈allTransforms) (kind : Fin 2)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10,t.applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints (auxKind kind))[(perm j).val]!)
    (i : Fin 12) (mask : t.maskAction w.mask=masks i)
    (ordinary : masks i∉auxExempt kind)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (t.pull (owners p i)).Inside ((auxPoints 1)[a.val]!).1 ((auxPoints 1)[a.val]!).2 ∨
    (t.pull (owners p i)).Inside ((auxPoints 1)[b.val]!).1 ((auxPoints 1)[b.val]!).2 ∨
    (t.pull (owners p i)).Inside ((auxPoints 1)[c.val]!).1 ((auxPoints 1)[c.val]!).2 := by
  let index := ownerIndex p (masks i)
  have code : markerCode p index=masks i :=
    CommonCases.OriginalOwners.code family p hf (masks i) (mask_member i)
  have exactMarkers : ExactMarkers (owners p i) (maskSupport (masks i)) := by
    change ExactMarkers (p.square index) (maskSupport (masks i))
    rw [←code]
    exact coded_exact p index
  have markers := exact_markers_pull t transform (owners p i) w.mask candidate
    (by simpa only [mask] using exactMarkers)
  have budget := nat_aux_budget p kind index
  rw [hf,code,exemption_count kind] at budget
  have bounds : 1≤(natAuxOwners p kind index).card ∧
      (natAuxOwners p kind index).card≤2 := by
    simpa only [ordinary,ite_false] using budget
  have allowed := CommonCases.DirectSingleBudget.transformed_actual w case979Family 1 kind
    checked t perm points p index markers (lower.trans bounds.1) (bounds.2.trans upper)
  have actual := CommonCases.DirectSingleBudget.pull_exact t (owners p i) 1 kind
    perm points (sortedAuxOwners p kind index) (nat_aux_exact p kind index)
  have point (j : Fin 10)
      (member : j.val∈RelaxedOwnerDomain.pulledOwners perm (sortedAuxOwners p kind index)) :
      (t.pull (owners p i)).Inside ((auxPoints 1)[j.val]!).1 ((auxPoints 1)[j.val]!).2 :=
    (actual j.val (by change j.val∈List.range 10; exact List.mem_range.mpr j.isLt)).mpr member
  rcases cover _ allowed with own | own | own
  · exact Or.inl (point a own)
  · exact Or.inr (Or.inl (point b own))
  · exact Or.inr (Or.inr (point c own))

/-- Swap, swap plus X, swap plus Y, and swap plus both reflections:
each map sends the complete G list to the indicated F list permutation. -/
def swapGF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![2,6,0,4,8,1,5,9,3,7] (by decide +kernel)
def swapXGF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![6,2,8,4,0,9,5,1,7,3] (by decide +kernel)
def swapYGF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![3,7,1,5,9,0,4,8,2,6] (by decide +kernel)
def swapXYGF : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![7,3,9,5,1,8,4,0,6,2] (by decide +kernel)
def reflectYG : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective ![1,0,4,3,2,7,6,5,9,8] (by decide +kernel)

theorem swapGF_points (j : Fin 10) :
    (⟨true,false,false⟩ : Transform).applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints 0)[(swapGF j).val]! := by fin_cases j <;> decide +kernel
theorem swapXGF_points (j : Fin 10) :
    (⟨true,true,false⟩ : Transform).applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints 0)[(swapXGF j).val]! := by fin_cases j <;> decide +kernel
theorem swapYGF_points (j : Fin 10) :
    (⟨true,false,true⟩ : Transform).applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints 0)[(swapYGF j).val]! := by fin_cases j <;> decide +kernel
theorem swapXYGF_points (j : Fin 10) :
    (⟨true,true,true⟩ : Transform).applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints 0)[(swapXYGF j).val]! := by fin_cases j <;> decide +kernel
theorem reflectYG_points (j : Fin 10) :
    (⟨false,false,true⟩ : Transform).applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints 1)[(reflectYG j).val]! := by fin_cases j <;> decide +kernel

theorem central_cover (t : Transform) (transform : t∈allTransforms) (kind : Fin 2)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10,t.applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints (auxKind kind))[(perm j).val]!)
    (i : Fin 12) (mask : t.maskAction 256=masks i) (ordinary : masks i∉auxExempt kind)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (t.pull (owners p i)).Inside 1 (8/5) ∨
    (t.pull (owners p i)).Inside (87/50) 1 ∨
    (t.pull (owners p i)).Inside (87/50) 2 := by
  have cover : ∀ s∈single979_5_1.allowed,0∈s ∨ 2∈s ∨ 3∈s := by decide +kernel
  simpa [auxPoints, gPoints] using transported_cover single979_5_1 single979_5_1_checked (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 2 3 cover t transform kind perm points
    i mask ordinary p hf

theorem wall_cover (t : Transform) (transform : t∈allTransforms) (kind : Fin 2)
    (perm : Fin 10 ≃ Fin 10)
    (points : ∀ j : Fin 10,t.applyRat ((auxPoints 1)[j.val]!)=
      (auxPoints (auxKind kind))[(perm j).val]!)
    (i : Fin 12) (mask : t.maskAction 4096=masks i) (ordinary : masks i∉auxExempt kind)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (t.pull (owners p i)).Inside 1 (8/5) ∨
    (t.pull (owners p i)).Inside 1 (12/5) ∨
    (t.pull (owners p i)).Inside (87/50) 2 := by
  have cover : ∀ s∈single979_8_1.allowed,0∈s ∨ 1∈s ∨ 3∈s := by decide +kernel
  simpa [auxPoints, gPoints] using transported_cover single979_8_1 single979_8_1_checked (by decide +kernel)
    (by decide +kernel) (by decide +kernel) 0 1 3 cover t transform kind perm points
    i mask ordinary p hf

end
#print axioms transported_cover
end N12Compact.Completion.OtherCases.C1089.AuxiliaryCover

/-! Original C1089 auxiliary covers, proved from its actual family4096.
Only two existing direct single-cover certificates are reused, under exact
whole-set coordinate permutations and the narrower true 1..2 budget.
Extra owned points remain permitted. No C1092 family theorem is applied,
and no finite component list, entrance count or case exclusion is assumed.
Source-only; these declarations have not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1089.AuxiliaryCover
open S12 S12Pilot OriginalData
set_option Elab.async false
noncomputable section

theorem southwest_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 4).Inside 1 (87/50) ∨ (owners p 4).Inside (8/5) 1 ∨
    (owners p 4).Inside 2 (87/50) := by
  have h := central_cover ⟨true,false,false⟩ (by decide +kernel) 0 swapGF swapGF_points
    4 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem southwest_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 4).Inside 1 (8/5) ∨ (owners p 4).Inside (87/50) 1 ∨
    (owners p 4).Inside (87/50) 2 := by
  have h := central_cover ⟨false,false,false⟩ (by decide +kernel) 1 (Equiv.refl (Fin 10))
    (by intro j; fin_cases j <;> rfl) 4 (by decide +kernel) (by decide +kernel) p hf
  simpa [inside_pull,Transform.apply] using h

theorem southeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 2 (87/50) ∨ (owners p 5).Inside (12/5) 1 ∨
    (owners p 5).Inside 3 (87/50) := by
  have h := central_cover ⟨true,true,false⟩ (by decide +kernel) 0 swapXGF swapXGF_points
    5 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem southeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside (113/50) 1 ∨ (owners p 5).Inside (113/50) 2 ∨
    (owners p 5).Inside 3 (8/5) := by
  have h := central_cover ⟨false,true,false⟩ (by decide +kernel) 1
    RelaxedOwnerDomain.reflectXG RelaxedOwnerDomain.reflectXG_points
    5 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 2 (113/50) ∨ (owners p 6).Inside (12/5) 3 ∨
    (owners p 6).Inside 3 (113/50) := by
  have h := central_cover ⟨true,true,true⟩ (by decide +kernel) 0 swapXYGF swapXYGF_points
    6 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (113/50) 2 ∨ (owners p 6).Inside (113/50) 3 ∨
    (owners p 6).Inside 3 (12/5) := by
  have h := central_cover ⟨false,true,true⟩ (by decide +kernel) 1
    RelaxedOwnerDomain.halfTurnPerm RelaxedOwnerDomain.halfTurnG_points
    6 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northwest_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 1 (113/50) ∨ (owners p 7).Inside (8/5) 3 ∨
    (owners p 7).Inside 2 (113/50) := by
  have h := central_cover ⟨true,false,true⟩ (by decide +kernel) 0 swapYGF swapYGF_points
    7 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem northwest_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 1 (12/5) ∨ (owners p 7).Inside (87/50) 2 ∨
    (owners p 7).Inside (87/50) 3 := by
  have h := central_cover ⟨false,false,true⟩ (by decide +kernel) 1 reflectYG reflectYG_points
    7 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem bottom_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (8/5) 1 ∨ (owners p 9).Inside 2 (87/50) ∨
    (owners p 9).Inside (12/5) 1 := by
  have h := wall_cover ⟨true,false,false⟩ (by decide +kernel) 0 swapGF swapGF_points
    9 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

/-- Additional literal wall covers reuse the same small certificate. -/
theorem top_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (8/5) 3 ∨ (owners p 11).Inside 2 (113/50) ∨
    (owners p 11).Inside (12/5) 3 := by
  have h := wall_cover ⟨true,false,true⟩ (by decide +kernel) 0 swapYGF swapYGF_points
    11 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

theorem right_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 10).Inside (113/50) 2 ∨ (owners p 10).Inside 3 (8/5) ∨
    (owners p 10).Inside 3 (12/5) := by
  have h := wall_cover ⟨false,true,false⟩ (by decide +kernel) 1
    RelaxedOwnerDomain.reflectXG RelaxedOwnerDomain.reflectXG_points
    10 (by decide +kernel) (by decide +kernel) p hf
  simp only [inside_pull] at h
  norm_num [Transform.apply] at h
  tauto

/-- The ordinary left owner keeps the full original G covering row. -/
theorem left_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 (8/5) ∨ (owners p 8).Inside 1 (12/5) ∨
    (owners p 8).Inside (87/50) 2 := by
  have h := wall_cover ⟨false,false,false⟩ (by decide +kernel) 1
    (Equiv.refl (Fin 10)) (by intro j; fin_cases j <;> rfl)
    8 (by decide +kernel) (by decide +kernel) p hf
  simpa [inside_pull,Transform.apply] using h

end
#print axioms southwest_f_cover
#print axioms northeast_f_cover
#print axioms northwest_g_cover
#print axioms bottom_f_cover
#print axioms top_f_cover
end N12Compact.Completion.OtherCases.C1089.AuxiliaryCover
