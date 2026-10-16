import Compact.Completion.CommonCases.C702Entrance
import Compact.Completion.CommonCases.SouthwestPoint
import Compact.Completion.CommonCases.MergedNearPoint

namespace N12Compact.CommonCases.C702
open S12 S12Pilot OriginalOwners
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (hm : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed family p hf mask hm P checked

structure OwnedPoints (p : NormalizedPacking) : Prop where
  bottomSingleton : ∀ x : ℝ, 28/25≤x → x≤87/50 → (owner p 1).Inside x 1
  leftSingleton : ∀ y : ℝ, 28/25≤y → y≤87/50 → (owner p 2).Inside 1 y
  topSingleton : ∀ x : ℝ, 113/50≤x → x≤72/25 → (owner p 16).Inside x 3
  rightSingleton : ∀ y : ℝ, 113/50≤y → y≤72/25 → (owner p 32).Inside 3 y
  southInward : (owner p 256).Inside 2 (87/50)
  southElbow : (owner p 256).Inside (87/50) 2
  rightInward : (owner p 16384).Inside 3 (87/50)
  rightOutward : (owner p 16384).Inside 3 (8/5)
  topLeft : (owner p 32768).Inside (8/5) 3
  topElbow : (owner p 32768).Inside (87/50) 3
  mergedInward : (owner p 1536).Inside 2 (113/50)
  mergedElbow : (owner p 1536).Inside (113/50) 2
  northInward : (owner p 6144).Inside 1 (113/50)

theorem owned_points (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : OwnedPoints p := by
  have oLo : (owner p 1).Inside (28/25) 1 := by
    have h := seed_point p hf 1 (by decide +kernel) (28/25,1) (by decide +kernel)
    norm_num at h; exact h
  have oHi : (owner p 1).Inside (87/50) 1 := by
    have h := seed_point p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have oSegment (x : ℝ) (lo : 28/25≤x) (hi : x≤87/50) : (owner p 1).Inside x 1 :=
    horizontal_segment _ _ _ _ _ oLo oHi (by norm_num) lo hi
  have vLo : (owner p 2).Inside 1 (28/25) := by
    have h := seed_point p hf 2 (by decide +kernel) (1,28/25) (by decide +kernel)
    norm_num at h; exact h
  have vHi : (owner p 2).Inside 1 (87/50) := by
    have h := seed_point p hf 2 (by decide +kernel) (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  have vSegment (y : ℝ) (lo : 28/25≤y) (hi : y≤87/50) : (owner p 2).Inside 1 y :=
    vertical_segment _ _ _ _ _ vLo vHi (by norm_num) lo hi
  have trLo : (owner p 16).Inside (113/50) 3 := by
    have h := seed_point p hf 16 (by decide +kernel) (113/50,3) (by decide +kernel)
    norm_num at h; exact h
  have trHi : (owner p 16).Inside (72/25) 3 := by
    have h := seed_point p hf 16 (by decide +kernel) (72/25,3) (by decide +kernel)
    norm_num at h; exact h
  have trSegment (x : ℝ) (lo : 113/50≤x) (hi : x≤72/25) : (owner p 16).Inside x 3 :=
    horizontal_segment _ _ _ _ _ trLo trHi (by norm_num) lo hi
  have nrLo : (owner p 32).Inside 3 (113/50) := by
    have h := seed_point p hf 32 (by decide +kernel) (3,113/50) (by decide +kernel)
    norm_num at h; exact h
  have nrHi : (owner p 32).Inside 3 (72/25) := by
    have h := seed_point p hf 32 (by decide +kernel) (3,72/25) (by decide +kernel)
    norm_num at h; exact h
  have nrSegment (y : ℝ) (lo : 113/50≤y) (hi : y≤72/25) : (owner p 32).Inside 3 y :=
    vertical_segment _ _ _ _ _ nrLo nrHi (by norm_num) lo hi
  have oPair := pair_from_points p 1 2 12 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact oSegment (8/5) (by norm_num) (by norm_num))
    (by norm_num [auxPoints,fPoints,gPoints]; exact oHi)
  have vPair := pair_from_points p 2 0 10 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact vHi)
    (by norm_num [auxPoints,fPoints,gPoints]; exact vSegment (8/5) (by norm_num) (by norm_num))
  have trPair := pair_from_points p 16 7 17 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact trSegment (12/5) (by norm_num) (by norm_num))
    (by norm_num [auxPoints,fPoints,gPoints]; exact trLo)
  have nrPair := pair_from_points p 32 9 19 (by norm_num) (by norm_num)
    (by norm_num [auxPoints,fPoints,gPoints]; exact nrLo)
    (by norm_num [auxPoints,fPoints,gPoints]; exact nrSegment (12/5) (by norm_num) (by norm_num))
  obtain ⟨aPair,bPair,rPair,tPair⟩ := base_pairs p hf oPair vPair trPair nrPair
  have aInward : (owner p 256).Inside 2 (87/50) := by
    have h := (auxiliary_exact p 256 4 (by norm_num)).mpr (aPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have aElbow : (owner p 256).Inside (87/50) 2 := by
    have h := (auxiliary_exact p 256 13 (by norm_num)).mpr (aPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have bOuter : (owner p 8192).Inside (12/5) 1 := by
    have h := (auxiliary_exact p 8192 6 (by norm_num)).mpr (bPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have bElbow : (owner p 8192).Inside (113/50) 1 := by
    have h := (auxiliary_exact p 8192 15 (by norm_num)).mpr (bPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have rInward : (owner p 16384).Inside 3 (87/50) := by
    have h := (auxiliary_exact p 16384 8 (by norm_num)).mpr (rPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have rOutward : (owner p 16384).Inside 3 (8/5) := by
    have h := (auxiliary_exact p 16384 18 (by norm_num)).mpr (rPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have tLeft : (owner p 32768).Inside (8/5) 3 := by
    have h := (auxiliary_exact p 32768 3 (by norm_num)).mpr (tPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have tElbow : (owner p 32768).Inside (87/50) 3 := by
    have h := (auxiliary_exact p 32768 14 (by norm_num)).mpr (tPair (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have markA : (owner p 256).Inside (33/20) (33/20) := by
    have h := seed_point p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markW0 : (owner p 1536).Inside (47/20) (33/20) := by
    have h := seed_point p hf 1536 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markW1 : (owner p 1536).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1536 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markR : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed_point p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have foreign (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
      (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun own => apart family p hf m n hm hn different _ _ ⟨own,point⟩
  have aNear := SouthwestPoint.point (owner p 256) (side p 256) markA aInward aElbow
    (foreign 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (vSegment (33/20) (by norm_num) (by norm_num)))
    (foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ oHi)
    (foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
      (oSegment (33/20) (by norm_num) (by norm_num)))
    (foreign 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ vHi)
  have wInward : (owner p 1536).Inside 2 (113/50) := by
    by_contra missing
    have wNear := MergedNearPoint.points_original (owner p 1536) (side p 1536) markW0 markW1
      (foreign 1536 256 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ aInward)
      missing
      (foreign 1536 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ rInward)
      (foreign 1536 32 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ nrLo)
      (foreign 1536 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markR)
    exact apart family p hf 256 1536 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨aNear,wNear.1⟩
  have wElbow : (owner p 1536).Inside (113/50) 2 := by
    obtain ⟨j,own⟩ := some_auxiliary p hf 1536 (by decide +kernel) 1 (by decide +kernel)
    fin_cases j
    all_goals norm_num [auxKind,auxPoints,fPoints,gPoints] at own
    · exact (foreign 1536 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (vSegment (8/5) (by norm_num) (by norm_num)) own).elim
    · have size : (owner p 1536).side≤1001/1000 := by
        change (p.square (ownerIndex p 1536)).side≤1001/1000
        rw [p.congruent]; exact p.side_le
      have distance := normalized_diameter_bound (owner p 1536) size 1 (12/5) (47/20) (33/20) own markW0
      norm_num at distance
    · exact (foreign 1536 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ oHi own).elim
    · exact (foreign 1536 256 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ aElbow own).elim
    · exact (foreign 1536 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ tElbow own).elim
    · exact (foreign 1536 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ bElbow own).elim
    · exact own
    · exact (foreign 1536 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ trLo own).elim
    · exact (foreign 1536 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ rOutward own).elim
    · exact (foreign 1536 32 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (nrSegment (12/5) (by norm_num) (by norm_num)) own).elim
  have nInward : (owner p 6144).Inside 1 (113/50) := by
    obtain ⟨j,own⟩ := some_auxiliary p hf 6144 (by decide +kernel) 0 (by decide +kernel)
    fin_cases j
    all_goals norm_num [auxKind,auxPoints,fPoints,gPoints] at own
    · exact (foreign 6144 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ vHi own).elim
    · exact own
    · exact (foreign 6144 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (oSegment (8/5) (by norm_num) (by norm_num)) own).elim
    · exact (foreign 6144 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ tLeft own).elim
    · exact (foreign 6144 256 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ aInward own).elim
    · exact (foreign 6144 1536 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ wInward own).elim
    · exact (foreign 6144 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ bOuter own).elim
    · exact (foreign 6144 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (trSegment (12/5) (by norm_num) (by norm_num)) own).elim
    · exact (foreign 6144 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ rInward own).elim
    · exact (foreign 6144 32 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ nrLo own).elim
  exact ⟨oSegment,vSegment,trSegment,nrSegment,aInward,aElbow,rInward,rOutward,
    tLeft,tElbow,wInward,wElbow,nInward⟩

#print axioms owned_points
end
end N12Compact.CommonCases.C702
