import Compact.Completion.OtherCases.MergedPending.CentralPoints
import Compact.Completion.OtherCases.ElbowPoint
import Compact.Completion.OtherCases.CrossedElbow
import Compact.Completion.OtherCases.OutwardBarPoint
import Compact.Completion.CommonCases.OutwardPoint

/-! Genuine southeast branches of C683 and C867. Marker14 is omitted by
the exact mask512 even in C683, which has no right-wall owner. Only that
literal point omission is used here. The entire bottom bar belongs to
actual8192 throughout. These producers do not exclude either family. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

private theorem southeast_marker (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k) :
    (owner p 512).Inside (47/20) (33/20) := by
  have point := seed _ p hf 512 member (47/20,33/20) (by decide +kernel)
  norm_num at point
  exact point

private theorem southeast_f8 (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k) :
    (owner p 512).Inside 3 (87/50) := by
  have point := (auxiliary_exact p 512 8 (by norm_num)).mpr (southeast_lower k p hf member)
  simpa [auxPoints,fPoints,gPoints] using point

private theorem southeast_bottom (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k)
    (x : ℝ) (low : 113/50≤x) (high : x≤14/5) :
    ¬(owner p 512).Inside x 1 := fun own =>
  apart _ p hf 512 8192 member (common_member k 8192 (by decide)) (by decide)
    _ _ ⟨own,(bottom_reach k p hf).2 x low high⟩

theorem southeast_g_cover (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k) :
    (owner p 512).Inside (113/50) 2 ∨ (owner p 512).Inside 3 (8/5) := by
  have w := walls k p hf
  have labels := common_labels k p hf
  have left := (auxiliary_exact p 4096 11 (by norm_num)).mpr labels.left.2
  have south := (auxiliary_exact p 256 13 (by norm_num)).mpr labels.south.2
  have top := (auxiliary_exact p 32768 14 (by norm_num)).mpr labels.top.2
  have bottom := (auxiliary_exact p 8192 15 (by norm_num)).mpr labels.bottom.2
  norm_num [auxPoints,fPoints,gPoints] at left south top bottom
  have ninth : ∃ m : Nat,m∈family k ∧ m≠512 ∧ (owner p m).Inside 3 (12/5) := by
    cases k with
    | c683 => exact ⟨32,by decide +kernel,by decide,
        c683_right_singleton p hf _ (by norm_num) (by norm_num)⟩
    | c700 => exact False.elim ((by decide +kernel : 512∉family .c700) member)
    | c867 =>
      refine ⟨16384,by decide +kernel,by decide,?_⟩
      have point := (auxiliary_exact p 16384 19 (by norm_num)).mpr (c867_right_labels p hf).2
      simpa [auxPoints,fPoints,gPoints] using point
  obtain ⟨right,rightMember,rightDifferent,rightPoint⟩ := ninth
  have foreign (m : Nat) (hm : m∈family k) (different : 512≠m)
      (x y : ℝ) (point : (owner p m).Inside x y) : ¬(owner p 512).Inside x y :=
    fun own => apart _ p hf 512 m member hm different _ _ ⟨own,point⟩
  have budget := (nat_aux_budget p 1 (ownerIndex p 512)).1
  rw [code _ p hf 512 member] at budget
  norm_num [auxExempt] at budget
  have positive : 0<(natAuxOwners p 1 (ownerIndex p 512)).card := by omega
  obtain ⟨j,owned⟩ := Finset.card_pos.mp positive
  have bound := Finset.mem_range.mp (nat_aux_subset p 1 (ownerIndex p 512) owned)
  have own := (nat_aux_exact p 1 (ownerIndex p 512) j
    (by simpa only [aux_kind_length] using List.mem_range.mpr bound)).mpr owned
  let index : Fin 10 := ⟨j,bound⟩
  change (owner p 512).Inside ((auxPoints (auxKind 1))[index.val]!).1
    ((auxPoints (auxKind 1))[index.val]!).2 at own
  fin_cases index
  all_goals norm_num [auxKind,auxPoints,fPoints,gPoints] at own
  · exact (foreign 2 (common_member k 2 (by decide)) (by decide) _ _
      (w.leftSingleton _ (by norm_num) (by norm_num)) own).elim
  · exact (foreign 4096 (common_member k 4096 (by decide)) (by decide) _ _ left own).elim
  · exact (foreign 1 (common_member k 1 (by decide)) (by decide) _ _
      (w.bottomSingleton _ (by norm_num) le_rfl) own).elim
  · exact (foreign 256 (common_member k 256 (by decide)) (by decide) _ _ south own).elim
  · exact (foreign 32768 (common_member k 32768 (by decide)) (by decide) _ _ top own).elim
  · exact (foreign 8192 (common_member k 8192 (by decide)) (by decide) _ _ bottom own).elim
  · exact Or.inl own
  · exact (foreign 16 (common_member k 16 (by decide)) (by decide) _ _
      (w.topSingleton _ le_rfl (by norm_num)) own).elim
  · exact Or.inr own
  · exact (foreign right rightMember (Ne.symm rightDifferent) _ _ rightPoint own).elim

theorem southeast_g8 (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k) :
    (owner p 512).Inside 3 (8/5) := by
  by_contra missing
  have inward := (southeast_g_cover k p hf member).resolve_right missing
  have north := missing_marker _ p hf 512 member 10 (by decide +kernel)
  have right := missing_marker _ p hf 512 member 14 (by decide +kernel)
  norm_num [S12.marker] at north right
  have duplicate := Completion.OtherCases.ElbowPoint.points_original _ (side p 512)
    (southeast_marker k p hf member) inward (southeast_f8 k p hf member) north missing right
  exact apart _ p hf 256 512 (common_member k 256 (by decide)) member (by decide)
    _ _ ⟨(southwest_crosspoints k p hf).1,duplicate.1⟩

theorem southeast_right_crosspoint (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k)
    (inward : (owner p 512).Inside (113/50) 2) :
    (owner p 512).Inside (5/2) 2 := by
  by_contra missing
  apply Completion.OtherCases.CrossedElbow.impossible_original (owner p 512)
    (4/5) (side p 512) (by norm_num) le_rfl
    (southeast_marker k p hf member) inward (southeast_f8 k p hf member) missing
  · exact fun own => apart _ p hf 256 512 (common_member k 256 (by decide)) member
      (by decide) _ _ ⟨(southwest_crosspoints k p hf).1,own⟩
  · norm_num only
    exact southeast_bottom k p hf member _ (by norm_num) le_rfl

theorem southeast_outward_frame (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    ∃ B : OpenSquare,0<B.c ∧ B.s<0 ∧ -B.s≤B.c ∧
      B.side=(owner p 512).side ∧
      (∀ x y,B.Inside x y↔(owner p 512).Inside x y) := by
  obtain ⟨B,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame (owner p 512)
  have size : 1<B.side := by simpa only [shape] using side p 512
  have right := missing_marker _ p hf 512 member 14 (by decide +kernel)
  have corner := seed _ p hf 12 (common_member k 12 (by decide)) (3,1) (by decide +kernel)
  norm_num [S12.marker] at right corner
  have sign : B.s<0 := by
    apply lt_of_not_ge
    intro nonnegative
    apply C981CompletionOutwardAnchor.nonnegative_impossible B size cp nonnegative
      (by simpa only [abs_of_nonneg nonnegative] using canonical)
      ((inside _ _).mpr (southeast_marker k p hf member))
      ((inside _ _).mpr (southeast_g8 k p hf member))
    · exact fun own => apart _ p hf 512 12 member (common_member k 12 (by decide))
        (by decide) _ _ ⟨(inside _ _).mp own,corner⟩
    · exact fun own => right ((inside _ _).mp own)
    · exact fun own => missing ((inside _ _).mp own)
    · exact fun x low high own => southeast_bottom k p hf member x low high ((inside _ _).mp own)
  exact ⟨B,cp,sign,by simpa only [abs_of_neg sign] using canonical,shape,inside⟩

theorem southeast_outward_points (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) (member : 512∈family k)
    (missing : ¬(owner p 512).Inside (113/50) 2) :
    (owner p 512).Inside (123/50) (201/100) ∧
      (owner p 512).Inside (101/40) (17/8) := by
  let q := pullY (owner p 512)
  have marker : q.Inside (47/20) (47/20) := by
    norm_num only [q,inside_pullY]
    exact southeast_marker k p hf member
  have outward : q.Inside 3 (113/50) := by
    norm_num only [q,inside_pullY]
    exact southeast_f8 k p hf member
  have upper : q.Inside 3 (12/5) := by
    norm_num only [q,inside_pullY]
    exact southeast_g8 k p hf member
  have inward : ¬q.Inside (113/50) 2 := by
    norm_num only [q,inside_pullY]
    exact missing
  have missingMarker := missing_marker _ p hf 512 member 14 (by decide +kernel)
  norm_num [S12.marker] at missingMarker
  have wall : ¬q.Inside (1543/500) 2 := by
    norm_num only [q,inside_pullY]
    exact missingMarker
  have corner (P : ℚ×ℚ) (checked : P∈seedPoints (maskSupport 12)) :
      ¬(owner p 512).Inside P.1 P.2 := fun own =>
    apart _ p hf 512 12 member (common_member k 12 (by decide)) (by decide)
      _ _ ⟨own,seed _ p hf 12 (common_member k 12 (by decide)) P checked⟩
  have missingCorner : ¬q.Inside 3 3 := by
    norm_num only [q,inside_pullY]
    simpa using corner (3,1) (by decide +kernel)
  have missingCornerMarker : ¬q.Inside (1543/500) 3 := by
    norm_num only [q,inside_pullY]
    simpa using corner (1543/500,1) (by decide +kernel)
  have bar (x : ℝ) (low : 113/50≤x) (high : x≤14/5) : ¬q.Inside x 3 := by
    norm_num only [q,inside_pullY]
    exact southeast_bottom k p hf member x low high
  have first := CommonCases.OutwardPoint.point_original q (side p 512)
    marker outward upper inward wall missingCorner missingCornerMarker bar
  have second := Completion.OtherCases.OutwardBarPoint.point_original q (side p 512)
    marker outward upper inward wall missingCorner missingCornerMarker bar
  norm_num only [q,inside_pullY] at first second
  exact ⟨first,second⟩

end
#print axioms southeast_g8
#print axioms southeast_right_crosspoint
#print axioms southeast_outward_frame
#print axioms southeast_outward_points
end N12Compact.MergedPending
