import Compact.Completion.CommonCases.C888C889Entrance
import Compact.Completion.CommonCases.CentralPair
import Compact.Completion.CommonCases.StrongBarPoint
import Compact.Completion.C981.WallAdvance
import Compact.Completion.C1092.MixedSpan
import Compact.Assembly.RowIdentity

/-! Complete original C888/C889 endings from their genuine shared entrance. -/
namespace N12Compact.CommonCases.C888C889
open S12 S12Pilot S12Completion OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

theorem family_impossible (b : Bool) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family b) : False := by
  obtain ⟨bottomAux,pattern⟩ := entrance b p hf
  have markA : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point b p hf 512 (by cases b <;> decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markN : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point b p hf 1024 (by cases b <;> decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markSW : (owner p 2304).Inside (33/20) (33/20) := by
    have h := seed_point b p hf 2304 (by cases b <;> decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markNW : (owner p 2304).Inside (33/20) (47/20) := by
    have h := seed_point b p hf 2304 (by cases b <;> decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markR : (owner p (rightMask b)).Inside (1543/500) 2 := by
    have h := seed_point b p hf (rightMask b) (by cases b <;> decide +kernel) (1543/500,2)
      (by cases b <;> decide +kernel)
    norm_num at h; exact h
  have bottomMarker : (owner p 8192).Inside 2 (457/500) := by
    have h := seed_point b p hf 8192 (by cases b <;> decide +kernel) (2,457/500) (by decide +kernel)
    norm_num at h; exact h
  have bottomElbow : (owner p 8192).Inside (113/50) 1 := by
    have h := auxiliary_point p 8192 _ bottomAux 15 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have bottomOuter : (owner p 8192).Inside (12/5) 1 := by
    have h := auxiliary_point p 8192 _ bottomAux 6 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have swTip : (owner p 1).Inside (87/50) 1 := by
    have h := seed_point b p hf 1 (by cases b <;> decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have swSeed : (owner p 1).Inside (187/100) (19/25) := by
    have h := seed_point b p hf 1 (by cases b <;> decide +kernel) (187/100,19/25) (by decide +kernel)
    norm_num at h; exact h
  have topElbow : (owner p 16).Inside (113/50) 3 := by
    have h := seed_point b p hf 16 (by cases b <;> decide +kernel) (113/50,3) (by decide +kernel)
    norm_num at h; exact h
  have topTip : (owner p 16).Inside (72/25) 3 := by
    have h := seed_point b p hf 16 (by cases b <;> decide +kernel) (72/25,3) (by decide +kernel)
    norm_num at h; exact h
  have topSegment (x : ℝ) (lo : 113/50≤x) (hi : x≤72/25) : (owner p 16).Inside x 3 :=
    horizontal_segment _ _ _ _ _ topElbow topTip (by norm_num) lo hi
  have seCorner : (owner p 12).Inside 3 1 := by
    have h := seed_point b p hf 12 (by cases b <;> decide +kernel) (3,1) (by decide +kernel)
    norm_num at h; exact h
  have seMarker : (owner p 12).Inside (1543/500) 1 := by
    have h := seed_point b p hf 12 (by cases b <;> decide +kernel) (1543/500,1) (by decide +kernel)
    norm_num at h; exact h
  have foreign (m n : Nat) (hm : m∈family b) (hn : n∈family b) (different : m≠n)
      (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun own => apart (family b) p hf m n hm hn different _ _ ⟨own,point⟩
  have bottomAdvance : (owner p 8192).Inside (14/5) 1 := by
    have h := C981CompletionWallAdvance.point (pullSwap (owner p 8192)) (side p 8192)
      (container_pullSwap _ (box p 8192))
      (by norm_num [inside_pullSwap]; exact bottomMarker)
      (by norm_num [inside_pullSwap]; exact bottomOuter)
      (by norm_num [inside_pullSwap]; exact (foreign 8192 1 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ swTip))
      (by norm_num [inside_pullSwap]; exact (foreign 8192 1 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ swSeed))
      (by norm_num [inside_pullSwap]; exact (foreign 8192 512 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ markA))
    simpa [inside_pullSwap] using h
  have bottomSegment (x : ℝ) (lo : 113/50≤x) (hi : x≤14/5) : (owner p 8192).Inside x 1 :=
    horizontal_segment _ _ _ _ _ bottomElbow bottomAdvance (by norm_num) lo hi
  rcases pattern with lower | upper
  · obtain ⟨aPair,nOptions⟩ := lower
    have inwardA : (owner p 512).Inside 2 (87/50) := by
      have h := auxiliary_point p 512 _ aPair 4 (by norm_num) (by decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h; exact h
    have elbowA : (owner p 512).Inside (113/50) 2 := by
      have h := auxiliary_point p 512 _ aPair 16 (by norm_num) (by decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h; exact h
    have missingG := foreign 1024 512 (by cases b <;> decide +kernel)
      (by cases b <;> decide +kernel) (by decide +kernel) _ _ elbowA
    have nUpper : (owner p 1024).Inside 3 (12/5) := by
      have checked : ∀ n∈([{5,19},{9,19},{5,9,19}] : List (Finset Nat)),19∈n := by decide +kernel
      have h := (auxiliary_exact p 1024 19 (by norm_num)).mpr (checked _ nOptions)
      norm_num [auxPoints,fPoints,gPoints] at h; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at nOptions
    rcases nOptions with mixed | outward | extra
    · apply C1092MixedSpan.impossible (pullY (owner p 1024)) (side p 1024)
      · norm_num [inside_pullY]
        have h := (auxiliary_exact p 1024 5 (by norm_num)).mpr (by rw [mixed]; decide +kernel)
        norm_num [auxPoints,fPoints,gPoints] at h; exact h
      · norm_num [inside_pullY]; exact nUpper
      · norm_num [inside_pullY]; exact missingG
      · norm_num [inside_pullY]
        have h := missing_auxiliary p 1024 _ mixed 9 (by norm_num) (by decide +kernel)
        norm_num [auxPoints,fPoints,gPoints] at h; exact h
      · norm_num [inside_pullY]
        exact foreign 1024 16 (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
          (by decide +kernel) _ _ topElbow
      · norm_num [inside_pullY]
        exact foreign 1024 16 (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
          (by decide +kernel) _ _ (topSegment (12/5) (by norm_num) (by norm_num))
    all_goals
      have nOutward : (owner p 1024).Inside 3 (113/50) := by
        have h := (auxiliary_exact p 1024 9 (by norm_num)).mpr
          (by first | rw [outward]; decide +kernel | rw [extra]; decide +kernel)
        norm_num [auxPoints,fPoints,gPoints] at h; exact h
      have inwardPoint := InwardPoint.point_original (owner p 512) (side p 512)
        markA inwardA elbowA
        (foreign 512 2304 (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
          (by decide +kernel) _ _ markSW)
        (foreign 512 1024 (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
          (by decide +kernel) _ _ markN)
        (foreign 512 8192 (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
          (by decide +kernel) _ _ bottomOuter)
      have missingH : ¬(owner p 1024).Inside (1543/500) 3 := by
        have h := missing_marker (family b) p hf 1024 (by cases b <;> decide +kernel) 5
          (by decide +kernel)
        norm_num [marker] at h; exact h
      have outwardPoint := StrongBarPoint.point_original (owner p 1024) (side p 1024)
        markN nOutward nUpper missingG
        (foreign 1024 (rightMask b) (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
          (by cases b <;> decide +kernel) _ _ markR) missingH
        (fun x lo hi => foreign 1024 16 (by cases b <;> decide +kernel)
          (by cases b <;> decide +kernel) (by decide +kernel) _ _
          (topSegment x lo (by linarith only [hi])))
      exact apart (family b) p hf 512 1024 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ ⟨inwardPoint,outwardPoint⟩
  · obtain ⟨nPair,aOptions⟩ := upper
    have inwardN : (owner p 1024).Inside 2 (113/50) := by
      have h := auxiliary_point p 1024 _ nPair 5 (by norm_num) (by decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h; exact h
    have elbowN : (owner p 1024).Inside (113/50) 2 := by
      have h := auxiliary_point p 1024 _ nPair 16 (by norm_num) (by decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h; exact h
    have pairA : ((pullY (owner p 512)).Inside 2 (113/50) ∧
        (pullY (owner p 512)).Inside 3 (12/5)) ∨
        ((pullY (owner p 512)).Inside 3 (113/50) ∧ (pullY (owner p 512)).Inside 3 (12/5)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at aOptions
      rcases aOptions with mixed | outward | extra
      · left; constructor
        · norm_num [inside_pullY]
          have h := (auxiliary_exact p 512 4 (by norm_num)).mpr (by rw [mixed]; decide +kernel)
          norm_num [auxPoints,fPoints,gPoints] at h; exact h
        · norm_num [inside_pullY]
          have h := (auxiliary_exact p 512 18 (by norm_num)).mpr (by rw [mixed]; decide +kernel)
          norm_num [auxPoints,fPoints,gPoints] at h; exact h
      all_goals
        right; constructor
        · norm_num [inside_pullY]
          have h := (auxiliary_exact p 512 8 (by norm_num)).mpr
            (by first | rw [outward]; decide +kernel | rw [extra]; decide +kernel)
          norm_num [auxPoints,fPoints,gPoints] at h; exact h
        · norm_num [inside_pullY]
          have h := (auxiliary_exact p 512 18 (by norm_num)).mpr
            (by first | rw [outward]; decide +kernel | rw [extra]; decide +kernel)
          norm_num [auxPoints,fPoints,gPoints] at h; exact h
    apply CentralPair.impossible (pullY (owner p 1024)) (pullY (owner p 512))
      (side p 1024) (side p 512)
      (by norm_num [inside_pullY]; exact markN)
      (by norm_num [inside_pullY]; exact inwardN)
      (by norm_num [inside_pullY]; exact elbowN)
      (by norm_num [inside_pullY]; exact (foreign 1024 2304 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ markNW))
      (by norm_num [inside_pullY]; exact (foreign 1024 16 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _
        (topSegment (12/5) (by norm_num) (by norm_num))))
      (by norm_num [inside_pullY]; exact markA) pairA
      (by norm_num [inside_pullY]; exact (foreign 512 (rightMask b) (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by cases b <;> decide +kernel) _ _ markR))
      (by norm_num [inside_pullY]; exact (foreign 512 12 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ seCorner))
      (by norm_num [inside_pullY]; exact (foreign 512 12 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _ seMarker))
    · intro x lo hi own
      exact foreign 512 8192 (by cases b <;> decide +kernel) (by cases b <;> decide +kernel)
        (by decide +kernel) _ _ (bottomSegment x lo hi)
        (by norm_num [inside_pullY] at own; exact own)
    · intro x y own
      exact apart (family b) p hf 1024 512 (by cases b <;> decide +kernel)
        (by cases b <;> decide +kernel) (by decide +kernel) _ _
        ⟨(inside_pullY _ _ _).mp own.1,(inside_pullY _ _ _).mp own.2⟩

private theorem row888_checked :
    (RowIdentity.rowAt 475).originalId=888 ∧ (RowIdentity.rowAt 475).groups=family false := by
  decide +kernel
private theorem row889_checked :
    (RowIdentity.rowAt 476).originalId=889 ∧ (RowIdentity.rowAt 476).groups=family true := by
  decide +kernel
theorem excludes888 : ExcludesCase 888 := by
  intro r hr he p hf
  exact family_impossible false p
    (hf.trans (RowIdentity.family_at 475 888 (family false) row888_checked r hr he))
theorem excludes889 : ExcludesCase 889 := by
  intro r hr he p hf
  exact family_impossible true p
    (hf.trans (RowIdentity.family_at 476 889 (family true) row889_checked r hr he))

#print axioms family_impossible
#print axioms excludes888
#print axioms excludes889
end
end N12Compact.CommonCases.C888C889
