import Compact.Completion.OtherCases.C974.OriginalData

/-! Actual C974 compulsory auxiliaries. Each finite step excludes only
points already strictly owned by a different displayed physical square. -/
namespace N12Compact.Completion.OtherCases.C974.OriginalData
open S12 S12Pilot N12Compact.FiniteCases
set_option Elab.async false
noncomputable section

structure Compulsory (p : NormalizedPacking) : Prop where
  southwestF4 : (owners p 5).Inside 2 (87/50)
  southwestG3 : (owners p 5).Inside (87/50) 2
  southeastF8 : (owners p 6).Inside 3 (87/50)
  southeastG : (owners p 6).Inside (113/50) 2 ∨ (owners p 6).Inside 3 (8/5)
  northeastF : (owners p 7).Inside 2 (113/50) ∨ (owners p 7).Inside (12/5) 3
  northeastG : (owners p 7).Inside (113/50) 2 ∨ (owners p 7).Inside (113/50) 3
  leftF1 : (owners p 8).Inside 1 (113/50)
  leftG1 : (owners p 8).Inside 1 (12/5)
  bottomF6 : (owners p 9).Inside (12/5) 1
  bottomG5 : (owners p 9).Inside (113/50) 1
  rightF9 : (owners p 10).Inside 3 (113/50)
  rightG9 : (owners p 10).Inside 3 (12/5)
  topComponent : (owners p 11).Inside (113/50) 3 ∨
    ((owners p 11).Inside (8/5) 3 ∧ (owners p 11).Inside (87/50) 3)

theorem compulsory (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Compulsory p := by
  have dom (d : CertifiedDomain family) (i : Fin 12) (equal : d.mask=masks i) :
      actual p i∈d.allowed := by
    have h := CommonCases.OriginalOwners.domain family d p hf (by rw [equal]; exact member i)
    change CommonCases.OriginalOwners.auxiliaries p (masks i)∈d.allowed
    simpa only [equal] using h
  have foreignAux (i j : Fin 12) (different : i≠j) (k : Nat)
      (own : k∈actual p j) : k∉actual p i :=
    fun other => Finset.disjoint_left.mp
      (CommonCases.OriginalOwners.auxiliary_disjoint family p hf (masks i) (masks j)
        (member i) (member j) (fun equal => different (injective equal))) other own
  have sw := C975FiniteCuts.southwest _ (dom Domains.southwest 0 rfl)
  have low := C975FiniteCuts.leftSingleton _ (dom Domains.leftSingleton 1 rfl)
  have bottom := C975FiniteCuts.bottom _ (dom Domains.bottom 9 rfl)
    (foreignAux 9 0 (by decide) 2 sw.1)
  have central := C975FiniteCuts.southwestCentral _ (dom Domains.southwestCentral 5 rfl)
    (foreignAux 5 1 (by decide) 0 low.1) (foreignAux 5 0 (by decide) 2 sw.1)
    (foreignAux 5 1 (by decide) 10 low.2) (foreignAux 5 0 (by decide) 12 sw.2)
  have left := C975FiniteCuts.leftWall _ (dom Domains.left 8 rfl)
    (foreignAux 8 1 (by decide) 0 low.1) (foreignAux 8 5 (by decide) 13 central.2)
  have south := C975FiniteCuts.southeast _ (dom Domains.southeast 6 rfl)
    (foreignAux 6 5 (by decide) 4 central.1) (foreignAux 6 9 (by decide) 6 bottom.1)
    (foreignAux 6 9 (by decide) 15 bottom.2)
  have right := C975FiniteCuts.rightWall _ (dom Domains.right 10 rfl)
    (foreignAux 10 6 (by decide) 8 south.1)
  have north := Domains.northeast_cut _ (dom Domains.northeast 7 rfl)
    (foreignAux 7 10 (by decide) 9 right.1) (foreignAux 7 10 (by decide) 19 right.2)
  have top := Domains.top_cut _ (dom Domains.top 11 rfl)
  refine {
    southwestF4 := ?_
    southwestG3 := ?_
    southeastF8 := ?_
    southeastG := ?_
    northeastF := ?_
    northeastG := ?_
    leftF1 := ?_
    leftG1 := ?_
    bottomF6 := ?_
    bottomG5 := ?_
    rightF9 := ?_
    rightG9 := ?_
    topComponent := ?_ }
  · simpa [auxPoints,fPoints,gPoints] using (aux p 5 4 (by norm_num)).mpr central.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 5 13 (by norm_num)).mpr central.2
  · simpa [auxPoints,fPoints,gPoints] using (aux p 6 8 (by norm_num)).mpr south.1
  · rcases south.2 with h | h
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 6 16 (by norm_num)).mpr h
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 6 18 (by norm_num)).mpr h
  · rcases north.1 with h | h
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 7 5 (by norm_num)).mpr h
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 7 7 (by norm_num)).mpr h
  · rcases north.2 with h | h
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 7 16 (by norm_num)).mpr h
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 7 17 (by norm_num)).mpr h
  · simpa [auxPoints,fPoints,gPoints] using (aux p 8 1 (by norm_num)).mpr left.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 8 11 (by norm_num)).mpr left.2
  · simpa [auxPoints,fPoints,gPoints] using (aux p 9 6 (by norm_num)).mpr bottom.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 9 15 (by norm_num)).mpr bottom.2
  · simpa [auxPoints,fPoints,gPoints] using (aux p 10 9 (by norm_num)).mpr right.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 10 19 (by norm_num)).mpr right.2
  · rcases top with h | h
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 11 17 (by norm_num)).mpr h
    · right
      exact ⟨by simpa [auxPoints,fPoints,gPoints] using (aux p 11 3 (by norm_num)).mpr h.1,
        by simpa [auxPoints,fPoints,gPoints] using (aux p 11 14 (by norm_num)).mpr h.2⟩

end
#print axioms compulsory
end N12Compact.Completion.OtherCases.C974.OriginalData
