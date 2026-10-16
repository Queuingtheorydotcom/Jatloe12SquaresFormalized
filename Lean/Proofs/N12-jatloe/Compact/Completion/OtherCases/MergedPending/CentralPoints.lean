import Compact.Completion.OtherCases.MergedPending.WallReach
import Compact.Completion.CommonCases.MergedNearPoint
import Compact.Completion.CommonCases.SouthwestPoint
import Compact.Completion.C981.Crosspoint

/-! Compulsory central points in the actual pending merged families.
The upper merged3072 is forced to F5 by genuine foreign F ownership.
C700's merged1536 is forced to F5 by the existing same-square merged
lemma, and to G6 by the actual G budget. Neither merged owner is split
into independent central squares. Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

private theorem some_auxiliary (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (mask : Nat) (member : mask∈family k)
    (kind : Fin 2) (ordinary : mask∉auxExempt kind) :
    ∃ j : Fin 10,(owner p mask).Inside ((auxPoints (auxKind kind))[j.val]!).1
      ((auxPoints (auxKind kind))[j.val]!).2 := by
  have budget := nat_aux_budget p kind (ownerIndex p mask)
  rw [code _ p hf mask member] at budget
  simp only [ordinary,if_false] at budget
  have positive : 0<(natAuxOwners p kind (ownerIndex p mask)).card :=
    lt_of_lt_of_le (by decide) budget.1
  obtain ⟨j,owned⟩ := Finset.card_pos.mp positive
  have bound := Finset.mem_range.mp (nat_aux_subset p kind (ownerIndex p mask) owned)
  refine ⟨⟨j,bound⟩,?_⟩
  exact (nat_aux_exact p kind (ownerIndex p mask) j
    (by simpa only [aux_kind_length] using List.mem_range.mpr bound)).mpr owned

theorem southwest_points (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) :
    (owner p 256).Inside 2 (87/50) ∧
      (owner p 256).Inside (87/50) 2 ∧
      (owner p 256).Inside (39/20) (39/20) := by
  have member := common_member k 256 (by decide)
  have labels := (common_labels k p hf).south
  have f := (auxiliary_exact p 256 4 (by norm_num)).mpr labels.1
  have g := (auxiliary_exact p 256 13 (by norm_num)).mpr labels.2
  have mark := seed _ p hf 256 member (33/20,33/20) (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints] at f g mark
  have w := walls k p hf
  have left := apart _ p hf 256 2 member (common_member k 2 (by decide)) (by decide)
  have bottom := apart _ p hf 256 1 member (common_member k 1 (by decide)) (by decide)
  have point := CommonCases.SouthwestPoint.point _ (side p 256) mark f g
    (fun own => left _ _ ⟨own,w.leftSingleton _ (by norm_num) (by norm_num)⟩)
    (fun own => bottom _ _ ⟨own,w.bottomSingleton _ (by norm_num) le_rfl⟩)
    (fun own => bottom _ _ ⟨own,w.bottomSingleton _ (by norm_num) (by norm_num)⟩)
    (fun own => left _ _ ⟨own,w.leftSingleton _ (by norm_num) le_rfl⟩)
  exact ⟨f,g,point⟩

theorem southwest_crosspoints (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) :
    (owner p 256).Inside 2 (3/2) ∧ (owner p 256).Inside (3/2) 2 := by
  have member := common_member k 256 (by decide)
  have points := southwest_points k p hf
  have w := walls k p hf
  have mark := seed _ p hf 256 member (33/20,33/20) (by decide +kernel)
  have north := missing_marker _ p hf 256 member 11 (by decide +kernel)
  have east := missing_marker _ p hf 256 member 9 (by decide +kernel)
  norm_num [S12.marker] at mark north east
  have left := apart _ p hf 256 2 member (common_member k 2 (by decide)) (by decide)
  have bottom := apart _ p hf 256 1 member (common_member k 1 (by decide)) (by decide)
  constructor
  · have point := C981CompletionCrosspoint.point (pullY (pullX (owner p 256))) (side p 256)
      (by norm_num [inside_pullX,inside_pullY]; exact points.1)
      (by norm_num [inside_pullX,inside_pullY]; exact points.2.1)
      (by norm_num [inside_pullX,inside_pullY]; exact mark)
      (by norm_num [inside_pullX,inside_pullY]; exact north)
      (by norm_num [inside_pullX,inside_pullY]; exact east)
      (by norm_num [inside_pullX,inside_pullY]
          exact fun own => left _ _ ⟨own,w.leftSingleton _ (by norm_num) (by norm_num)⟩)
      (by norm_num [inside_pullX,inside_pullY]
          exact fun own => left _ _ ⟨own,w.leftSingleton _ (by norm_num) (by norm_num)⟩)
    norm_num [inside_pullX,inside_pullY] at point
    exact point
  · let t : Transform := ⟨true,true,true⟩
    have point := C981CompletionCrosspoint.point (t.pull (owner p 256)) (side p 256)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact points.2.1)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact points.1)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact mark)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact east)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact north)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
          exact fun own => bottom _ _ ⟨own,w.bottomSingleton _ (by norm_num) (by norm_num)⟩)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
          exact fun own => bottom _ _ ⟨own,w.bottomSingleton _ (by norm_num) (by norm_num)⟩)
    norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at point
    exact point

/-- This F5 belongs to the one actual upper merged square in both
C683 and C867. C700 has no such owner and is excluded by membership. -/
theorem upper_merged_inward (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 3072∈family k) :
    (owner p 3072).Inside 2 (113/50) := by
  have se : 512∈family k := by
    cases k with
    | c683 => decide +kernel
    | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) member)
    | c867 => decide +kernel
  have ninth : ∃ m : Nat,m∈family k ∧ m≠3072 ∧ (owner p m).Inside 3 (113/50) := by
    cases k with
    | c683 => exact ⟨32,by decide +kernel,by decide,c683_right_singleton p hf _ le_rfl (by norm_num)⟩
    | c700 => exact False.elim ((by decide +kernel : 3072∉family .c700) member)
    | c867 =>
      refine ⟨16384,by decide +kernel,by decide,?_⟩
      have point := (auxiliary_exact p 16384 9 (by norm_num)).mpr (c867_right_labels p hf).1
      simpa [auxPoints,fPoints,gPoints] using point
  obtain ⟨right,rightMember,rightDifferent,rightPoint⟩ := ninth
  have w := walls k p hf
  have l := common_labels k p hf
  have leftF := (auxiliary_exact p 4096 1 (by norm_num)).mpr l.left.1
  have topF := (auxiliary_exact p 32768 3 (by norm_num)).mpr l.top.1
  have southF := (auxiliary_exact p 256 4 (by norm_num)).mpr l.south.1
  have bottomF := (auxiliary_exact p 8192 6 (by norm_num)).mpr l.bottom.1
  have southeastF := (auxiliary_exact p 512 8 (by norm_num)).mpr (southeast_lower k p hf se)
  norm_num [auxPoints,fPoints,gPoints] at leftF topF southF bottomF southeastF
  have foreign (m : Nat) (hm : m∈family k) (different : 3072≠m)
      (x y : ℝ) (point : (owner p m).Inside x y) : ¬(owner p 3072).Inside x y :=
    fun own => apart _ p hf 3072 m member hm different _ _ ⟨own,point⟩
  obtain ⟨j,own⟩ := some_auxiliary k p hf 3072 member 0 (by decide +kernel)
  fin_cases j
  all_goals norm_num [auxKind,auxPoints,fPoints,gPoints] at own
  · exact (foreign 2 (common_member k 2 (by decide)) (by decide) _ _
      (w.leftSingleton _ (by norm_num) le_rfl) own).elim
  · exact (foreign 4096 (common_member k 4096 (by decide)) (by decide) _ _ leftF own).elim
  · exact (foreign 1 (common_member k 1 (by decide)) (by decide) _ _
      (w.bottomSingleton _ (by norm_num) (by norm_num)) own).elim
  · exact (foreign 32768 (common_member k 32768 (by decide)) (by decide) _ _ topF own).elim
  · exact (foreign 256 (common_member k 256 (by decide)) (by decide) _ _ southF own).elim
  · exact own
  · exact (foreign 8192 (common_member k 8192 (by decide)) (by decide) _ _ bottomF own).elim
  · exact (foreign 16 (common_member k 16 (by decide)) (by decide) _ _
      (w.topSingleton _ (by norm_num) (by norm_num)) own).elim
  · exact (foreign 512 se (by decide) _ _ southeastF own).elim
  · exact (foreign right rightMember (Ne.symm rightDifferent) _ _ rightPoint own).elim

theorem c700_merged_elbow (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 1536).Inside (113/50) 2 := by
  have w := walls .c700 p hf
  have l := common_labels .c700 p hf
  have leftG := (auxiliary_exact p 4096 11 (by norm_num)).mpr l.left.2
  have topG := (auxiliary_exact p 32768 14 (by norm_num)).mpr l.top.2
  have southG := (auxiliary_exact p 256 13 (by norm_num)).mpr l.south.2
  have bottomG := (auxiliary_exact p 8192 15 (by norm_num)).mpr l.bottom.2
  have rightG := (auxiliary_exact p 16384 18 (by norm_num)).mpr (c700_right_labels p hf).2
  norm_num [auxPoints,fPoints,gPoints] at leftG topG southG bottomG rightG
  have foreign (m : Nat) (hm : m∈family .c700) (different : 1536≠m)
      (x y : ℝ) (point : (owner p m).Inside x y) : ¬(owner p 1536).Inside x y :=
    fun own => apart _ p hf 1536 m (by decide +kernel) hm different _ _ ⟨own,point⟩
  obtain ⟨j,own⟩ := some_auxiliary .c700 p hf 1536 (by decide +kernel) 1 (by decide +kernel)
  fin_cases j
  all_goals norm_num [auxKind,auxPoints,fPoints,gPoints] at own
  · exact (foreign 2 (by decide +kernel) (by decide) _ _
      (w.leftSingleton _ (by norm_num) (by norm_num)) own).elim
  · exact (foreign 4096 (by decide +kernel) (by decide) _ _ leftG own).elim
  · exact (foreign 1 (by decide +kernel) (by decide) _ _
      (w.bottomSingleton _ (by norm_num) le_rfl) own).elim
  · exact (foreign 256 (by decide +kernel) (by decide) _ _ southG own).elim
  · exact (foreign 32768 (by decide +kernel) (by decide) _ _ topG own).elim
  · exact (foreign 8192 (by decide +kernel) (by decide) _ _ bottomG own).elim
  · exact own
  · exact (foreign 16 (by decide +kernel) (by decide) _ _
      (w.topSingleton _ le_rfl (by norm_num)) own).elim
  · exact (foreign 16384 (by decide +kernel) (by decide) _ _ rightG own).elim
  · exact (foreign 32 (by decide +kernel) (by decide) _ _
      (c700_right_singleton p hf _ (by norm_num) (by norm_num)) own).elim

theorem c700_merged_inward (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 1536).Inside 2 (113/50) := by
  have south := southwest_points .c700 p hf
  have marks := c700_merged_markers p hf
  have rightF := (auxiliary_exact p 16384 8 (by norm_num)).mpr (c700_right_labels p hf).1
  have rightMarker := seed _ p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints] at rightF rightMarker
  have foreign (m : Nat) (hm : m∈family .c700) (different : 1536≠m)
      (x y : ℝ) (point : (owner p m).Inside x y) : ¬(owner p 1536).Inside x y :=
    fun own => apart _ p hf 1536 m (by decide +kernel) hm different _ _ ⟨own,point⟩
  by_contra missing
  have near := CommonCases.MergedNearPoint.points_original _ (side p 1536) marks.1 marks.2
    (foreign 256 (by decide +kernel) (by decide) _ _ south.1) missing
    (foreign 16384 (by decide +kernel) (by decide) _ _ rightF)
    (foreign 32 (by decide +kernel) (by decide) _ _
      (c700_right_singleton p hf _ le_rfl (by norm_num)))
    (foreign 16384 (by decide +kernel) (by decide) _ _ rightMarker)
  exact apart _ p hf 256 1536 (by decide +kernel) (by decide +kernel) (by decide)
    _ _ ⟨south.2.2,near.1⟩

end
#print axioms southwest_crosspoints
#print axioms upper_merged_inward
#print axioms c700_merged_elbow
#print axioms c700_merged_inward
end N12Compact.MergedPending
