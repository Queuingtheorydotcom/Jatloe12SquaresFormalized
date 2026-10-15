import Compact.Completion.FiniteCases.C972Owners

/-! The actual C972 compulsory entrance. It retains both G alternatives
in the right central owners and does not invent an ordinary top square. -/
namespace N12Compact.FiniteCases.C972
open S12 S12Pilot
set_option Elab.async false
noncomputable section

structure Compulsory (p : NormalizedPacking) : Prop where
  singleton0 : 2∈actual p 0 ∧ 12∈actual p 0
  singleton1 : 0∈actual p 1 ∧ 10∈actual p 1
  southwest : 4∈actual p 5 ∧ 13∈actual p 5
  southeast : 8∈actual p 6 ∧ (16∈actual p 6 ∨ 18∈actual p 6)
  northeast : (5∈actual p 7 ∨ 7∈actual p 7) ∧ (16∈actual p 7 ∨ 17∈actual p 7)
  left : 1∈actual p 9 ∧ 11∈actual p 9
  bottom : 6∈actual p 10 ∧ 15∈actual p 10
  right : 9∈actual p 11 ∧ 19∈actual p 11

theorem compulsory (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    Compulsory p := by
  have sw := C975FiniteCuts.southwest _ (domain p hf C972Domains.southwest 0 rfl)
  have low := C975FiniteCuts.leftSingleton _ (domain p hf C972Domains.leftSingleton 1 rfl)
  have bottom := C975FiniteCuts.bottom _ (domain p hf C972Domains.bottom 10 rfl)
    (foreign_aux p hf 10 0 (by decide) 2 sw.1)
  have central := C975FiniteCuts.southwestCentral _ (domain p hf C972Domains.southwestCentral 5 rfl)
    (foreign_aux p hf 5 1 (by decide) 0 low.1) (foreign_aux p hf 5 0 (by decide) 2 sw.1)
    (foreign_aux p hf 5 1 (by decide) 10 low.2) (foreign_aux p hf 5 0 (by decide) 12 sw.2)
  have left := C975FiniteCuts.leftWall _ (domain p hf C972Domains.left 9 rfl)
    (foreign_aux p hf 9 1 (by decide) 0 low.1) (foreign_aux p hf 9 5 (by decide) 13 central.2)
  have south := C975FiniteCuts.southeast _ (domain p hf C972Domains.southeast 6 rfl)
    (foreign_aux p hf 6 5 (by decide) 4 central.1) (foreign_aux p hf 6 10 (by decide) 6 bottom.1)
    (foreign_aux p hf 6 10 (by decide) 15 bottom.2)
  have right := C975FiniteCuts.rightWall _ (domain p hf C972Domains.right 11 rfl)
    (foreign_aux p hf 11 6 (by decide) 8 south.1)
  have north := C972Domains.northeast_cut _ (domain p hf C972Domains.northeast 7 rfl)
    (foreign_aux p hf 7 11 (by decide) 9 right.1) (foreign_aux p hf 7 11 (by decide) 19 right.2)
  exact ⟨sw,low,central,south,north,left,bottom,right⟩

structure Points (p : NormalizedPacking) : Prop where
  southwestF4 : (owners p 5).Inside 2 (87/50)
  southwestG3 : (owners p 5).Inside (87/50) 2
  southeastF8 : (owners p 6).Inside 3 (87/50)
  southeastG : (owners p 6).Inside (113/50) 2 ∨ (owners p 6).Inside 3 (8/5)
  northeastF : (owners p 7).Inside 2 (113/50) ∨ (owners p 7).Inside (12/5) 3
  northeastG : (owners p 7).Inside (113/50) 2 ∨ (owners p 7).Inside (113/50) 3
  leftF1 : (owners p 9).Inside 1 (113/50)
  leftG1 : (owners p 9).Inside 1 (12/5)
  bottomF6 : (owners p 10).Inside (12/5) 1
  bottomG5 : (owners p 10).Inside (113/50) 1
  rightF9 : (owners p 11).Inside 3 (113/50)
  rightG9 : (owners p 11).Inside 3 (12/5)

theorem points (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : Points p := by
  have h := compulsory p hf
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [auxPoints,fPoints,gPoints] using (aux p 5 4 (by norm_num)).mpr h.southwest.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 5 13 (by norm_num)).mpr h.southwest.2
  · simpa [auxPoints,fPoints,gPoints] using (aux p 6 8 (by norm_num)).mpr h.southeast.1
  · rcases h.southeast.2 with g|g
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 6 16 (by norm_num)).mpr g
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 6 18 (by norm_num)).mpr g
  · rcases h.northeast.1 with f|f
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 7 5 (by norm_num)).mpr f
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 7 7 (by norm_num)).mpr f
  · rcases h.northeast.2 with g|g
    · left; simpa [auxPoints,fPoints,gPoints] using (aux p 7 16 (by norm_num)).mpr g
    · right; simpa [auxPoints,fPoints,gPoints] using (aux p 7 17 (by norm_num)).mpr g
  · simpa [auxPoints,fPoints,gPoints] using (aux p 9 1 (by norm_num)).mpr h.left.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 9 11 (by norm_num)).mpr h.left.2
  · simpa [auxPoints,fPoints,gPoints] using (aux p 10 6 (by norm_num)).mpr h.bottom.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 10 15 (by norm_num)).mpr h.bottom.2
  · simpa [auxPoints,fPoints,gPoints] using (aux p 11 9 (by norm_num)).mpr h.right.1
  · simpa [auxPoints,fPoints,gPoints] using (aux p 11 19 (by norm_num)).mpr h.right.2

end
#print axioms compulsory
end N12Compact.FiniteCases.C972
