import Compact.Completion.OtherCases.C976.OriginalData

/-! Small exact cuts of C976's authentic saved domains. The queries and
their inherited native verification sites remain in S12.Case976Domains;
all new finite deductions use kernel decision proofs. Complete local
ownership and all additional allowed points are retained. -/
namespace N12Compact.Completion.OtherCases.C976.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem single_cover (w : DirectSingleDomain) (k : Fin 2)
    (checked : w.Check family k) (i : Fin 12) (mask : w.mask=masks i)
    (a b c : Fin 10) (cut : ∀ s∈w.allowed,a.val∈s ∨ b.val∈s ∨ c.val∈s)
    (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p i).Inside ((auxPoints (auxKind k))[a.val]!).1 ((auxPoints (auxKind k))[a.val]!).2 ∨
    (owners p i).Inside ((auxPoints (auxKind k))[b.val]!).1 ((auxPoints (auxKind k))[b.val]!).2 ∨
    (owners p i).Inside ((auxPoints (auxKind k))[c.val]!).1 ((auxPoints (auxKind k))[c.val]!).2 := by
  have code := CommonCases.OriginalOwners.code family p hf (masks i) (member i)
  have allowed := w.actual family k checked p (ownerIndex p (masks i)) hf (code.trans mask.symm)
  have exactPoints := nat_aux_exact p k (ownerIndex p (masks i))
  have point (j : Fin 10) (own : j.val∈natAuxOwners p k (ownerIndex p (masks i))) :
      (owners p i).Inside ((auxPoints (auxKind k))[j.val]!).1
        ((auxPoints (auxKind k))[j.val]!).2 :=
    (exactPoints j.val (by change j.val∈List.range 10; exact List.mem_range.mpr j.isLt)).mpr own
  rcases cut _ allowed with own | own | own
  · exact Or.inl (point a own)
  · exact Or.inr (Or.inl (point b own))
  · exact Or.inr (Or.inr (point c own))

theorem southwest_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 1 (87/50) ∨ (owners p 5).Inside (8/5) 1 ∨
      (owners p 5).Inside 2 (87/50) := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_5_0 0
    single976_5_0_checked 5 rfl 0 2 4 (by decide +kernel) p hf
theorem southwest_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 5).Inside 1 (8/5) ∨ (owners p 5).Inside (87/50) 1 ∨
      (owners p 5).Inside (87/50) 2 := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_5_1 1
    single976_5_1_checked 5 rfl 0 2 3 (by decide +kernel) p hf
theorem bottom_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (8/5) 1 ∨ (owners p 9).Inside 2 (87/50) ∨
      (owners p 9).Inside (12/5) 1 := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_9_0 0
    single976_9_0_checked 9 rfl 2 4 6 (by decide +kernel) p hf
theorem bottom_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 9).Inside (87/50) 1 ∨ (owners p 9).Inside (113/50) 1 := by
  have h := single_cover single976_9_1 1 single976_9_1_checked 9 rfl 2 5 5
    (by decide +kernel) p hf
  simpa [auxKind,auxPoints,fPoints,gPoints,or_self] using h
theorem southeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside 2 (87/50) ∨ (owners p 6).Inside (12/5) 1 ∨
      (owners p 6).Inside 3 (87/50) := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_6_0 0
    single976_6_0_checked 6 rfl 4 6 8 (by decide +kernel) p hf
theorem southeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 6).Inside (113/50) 1 ∨ (owners p 6).Inside (113/50) 2 ∨
      (owners p 6).Inside 3 (8/5) := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_6_1 1
    single976_6_1_checked 6 rfl 5 6 8 (by decide +kernel) p hf
theorem northeast_f_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside 2 (113/50) ∨ (owners p 7).Inside (12/5) 3 ∨
      (owners p 7).Inside 3 (113/50) := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_7_0 0
    single976_7_0_checked 7 rfl 5 7 9 (by decide +kernel) p hf
theorem northeast_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 7).Inside (113/50) 2 ∨ (owners p 7).Inside (113/50) 3 ∨
      (owners p 7).Inside 3 (12/5) := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_7_1 1
    single976_7_1_checked 7 rfl 6 7 9 (by decide +kernel) p hf
theorem left_g_cover (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 (8/5) ∨ (owners p 8).Inside 1 (12/5) ∨
      (owners p 8).Inside (87/50) 2 := by
  simpa [auxKind,auxPoints,fPoints,gPoints] using single_cover single976_8_1 1
    single976_8_1_checked 8 rfl 0 1 3 (by decide +kernel) p hf

theorem right_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missing : ¬(owners p 10).Inside 3 (87/50)) :
    (owners p 10).Inside 3 (113/50) ∧ (owners p 10).Inside 3 (12/5) := by
  have allowed := CommonCases.OriginalOwners.domain family domain976_10_19 p hf (by decide +kernel)
  have cut : ∀ s∈domain976_10_19.allowed,8∉s → 9∈s ∧ 19∈s := by decide +kernel
  have no : 8∉actual p 10 := by
    intro own; apply missing; simpa [auxPoints,fPoints,gPoints] using (aux p 10 8 (by norm_num)).mpr own
  have pair := cut _ allowed no
  exact ⟨by simpa [auxPoints,fPoints,gPoints] using (aux p 10 9 (by norm_num)).mpr pair.1,
    by simpa [auxPoints,fPoints,gPoints] using (aux p 10 19 (by norm_num)).mpr pair.2⟩

theorem top_component (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (113/50) 3 ∨
      ((owners p 11).Inside (8/5) 3 ∧ (owners p 11).Inside (87/50) 3) := by
  have allowed := CommonCases.OriginalOwners.domain family domain976_11_19 p hf (by decide +kernel)
  have cut : ∀ s∈domain976_11_19.allowed,17∈s ∨ (3∈s ∧ 14∈s) := by decide +kernel
  rcases cut _ allowed with own | pair
  · left; simpa [auxPoints,fPoints,gPoints] using (aux p 11 17 (by norm_num)).mpr own
  · right
    exact ⟨by simpa [auxPoints,fPoints,gPoints] using (aux p 11 3 (by norm_num)).mpr pair.1,
      by simpa [auxPoints,fPoints,gPoints] using (aux p 11 14 (by norm_num)).mpr pair.2⟩

theorem left_f1_of_g1 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (g1 : (owners p 8).Inside 1 (12/5)) : (owners p 8).Inside 1 (113/50) := by
  have allowed := CommonCases.OriginalOwners.domain family domain976_8_61 p hf (by decide +kernel)
  have cut : ∀ s∈domain976_8_61.allowed,11∈s → 1∈s := by decide +kernel
  have own : 11∈actual p 8 := (aux p 8 11 (by norm_num)).mp (by
    simpa [auxPoints,fPoints,gPoints] using g1)
  simpa [auxPoints,fPoints,gPoints] using (aux p 8 1 (by norm_num)).mpr (cut _ allowed own)

end
#print axioms right_pair
#print axioms top_component
#print axioms left_f1_of_g1
end N12Compact.Completion.OtherCases.C976.OriginalData
