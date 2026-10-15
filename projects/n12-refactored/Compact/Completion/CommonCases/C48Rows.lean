import Compact.Completion.CommonCases.C48Entrance
import Compact.Completion.CommonCases.SouthwestPoint
import Compact.Completion.CommonCases.MergedNearPoint
import Compact.Completion.CommonCases.NorthwestSharpPoint
import Compact.Completion.CommonCases.MergedInwardPoint
import Compact.Completion.C981.WallAdvance
import Compact.Completion.C981.WallOrigin
import Compact.Completion.C981.Charts
import Compact.Assembly.RowIdentity

/-! Complete original C48/C573/C574. The varying bottom owner keeps its
actual original mask. The NE paired corner supplies a genuine whole
vertical segment, and two distinct actual central owners share 1.95,1.95. -/
namespace N12Compact.CommonCases.C48Rows
open S12 S12Pilot S12Completion OriginalOwners
noncomputable section
set_option Elab.async false

theorem family_impossible (k : Kind) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) : False := by
  have pairs := entrance k p hf
  have aP : (owner p 256).Inside (2) (87/50) := by
    have h := auxiliary_point p 256 _ pairs.southwest 4 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have aD : (owner p 256).Inside (87/50) (2) := by
    have h := auxiliary_point p 256 _ pairs.southwest 13 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have iF : (owner p 8).Inside (3) (87/50) := by
    have h := auxiliary_point p 8 _ pairs.rightSingleton 8 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have rF : (owner p 16384).Inside (3) (113/50) := by
    have h := auxiliary_point p 16384 _ pairs.rightWall 9 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have rG : (owner p 16384).Inside (3) (12/5) := by
    have h := auxiliary_point p 16384 _ pairs.rightWall 19 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have tF : (owner p 32768).Inside (12/5) (3) := by
    have h := auxiliary_point p 32768 _ pairs.topWall 7 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have tG : (owner p 32768).Inside (113/50) (3) := by
    have h := auxiliary_point p 32768 _ pairs.topWall 17 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have lF : (owner p 4096).Inside (1) (113/50) := by
    have h := auxiliary_point p 4096 _ pairs.leftWall 1 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have lG : (owner p 4096).Inside (1) (12/5) := by
    have h := auxiliary_point p 4096 _ pairs.leftWall 11 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have markA : (owner p 256).Inside (33/20) (33/20) := by
    have h := seed_point k p hf 256 (by cases k <;> decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markW0 : (owner p 1536).Inside (47/20) (33/20) := by
    have h := seed_point k p hf 1536 (by cases k <;> decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markW1 : (owner p 1536).Inside (47/20) (47/20) := by
    have h := seed_point k p hf 1536 (by cases k <;> decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markN : (owner p 2048).Inside (33/20) (47/20) := by
    have h := seed_point k p hf 2048 (by cases k <;> decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markL : (owner p 4096).Inside (457/500) (2) := by
    have h := seed_point k p hf 4096 (by cases k <;> decide +kernel) (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  have markR : (owner p 16384).Inside (1543/500) (2) := by
    have h := seed_point k p hf 16384 (by cases k <;> decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have markT : (owner p 32768).Inside (2) (1543/500) := by
    have h := seed_point k p hf 32768 (by cases k <;> decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have cornerK : (owner p 192).Inside (1) (3) := by
    have h := seed_point k p hf 192 (by cases k <;> decide +kernel) (1,3) (by decide +kernel)
    norm_num at h; exact h
  have cornerE : (owner p 48).Inside (3) (3) := by
    have h := seed_point k p hf 48 (by cases k <;> decide +kernel) (3,3) (by decide +kernel)
    norm_num at h; exact h
  have vDeep : (owner p 2).Inside (19/25) (187/100) := by
    have h := seed_point k p hf 2 (by cases k <;> decide +kernel) (19/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  have iDeep : (owner p 8).Inside (81/25) (187/100) := by
    have h := seed_point k p hf 8 (by cases k <;> decide +kernel) (81/25,187/100) (by decide +kernel)
    norm_num at h; exact h
  have oLo : (owner p 1).Inside (28/25) (1) := by
    have h := seed_point k p hf 1 (by cases k <;> decide +kernel) (28/25,1) (by decide +kernel)
    norm_num at h; exact h
  have oHi : (owner p 1).Inside (87/50) (1) := by
    have h := seed_point k p hf 1 (by cases k <;> decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have vLo : (owner p 2).Inside (1) (28/25) := by
    have h := seed_point k p hf 2 (by cases k <;> decide +kernel) (1,28/25) (by decide +kernel)
    norm_num at h; exact h
  have vHi : (owner p 2).Inside (1) (87/50) := by
    have h := seed_point k p hf 2 (by cases k <;> decide +kernel) (1,87/50) (by decide +kernel)
    norm_num at h; exact h
  have oSegment (x : ℝ) (lo : 28/25≤x) (hi : x≤87/50) : (owner p 1).Inside x 1 :=
    horizontal_segment _ _ _ _ _ oLo oHi (by norm_num) lo hi
  have vSegment (y : ℝ) (lo : 28/25≤y) (hi : y≤87/50) : (owner p 2).Inside 1 y :=
    vertical_segment _ _ _ _ _ vLo vHi (by norm_num) lo hi
  have foreign (m n : Nat) (hm : m∈family k) (hn : n∈family k) (different : m≠n)
      (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun own => apart (family k) p hf m n hm hn different _ _ ⟨own,point⟩
  have aNear := SouthwestPoint.point (owner p 256) (side p 256) markA aP aD
    (foreign 256 2 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ (vSegment (33/20) (by norm_num) (by norm_num)))
    (foreign 256 1 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ oHi)
    (foreign 256 1 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ (oSegment (33/20) (by norm_num) (by norm_num)))
    (foreign 256 2 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ vHi)
  have wF : (owner p 1536).Inside 2 (113/50) := by
    by_contra missing
    have wNear := MergedNearPoint.points_original (owner p 1536) (side p 1536) markW0 markW1
      (foreign 1536 256 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ aP) missing
      (foreign 1536 8 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ iF)
      (foreign 1536 16384 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ rF)
      (foreign 1536 16384 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ markR)
    exact apart (family k) p hf 256 1536 (by cases k <;> decide +kernel)
      (by cases k <;> decide +kernel) (by decide +kernel) _ _ ⟨aNear,wNear.1⟩
  have nPair := north_outward k p hf pairs wF
  have nF : (owner p 2048).Inside (8/5) 3 := by
    have h := auxiliary_point p 2048 _ nPair 3 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have nG : (owner p 2048).Inside (87/50) 3 := by
    have h := auxiliary_point p 2048 _ nPair 14 (by norm_num) (by decide +kernel)
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have lFar : (owner p 4096).Inside 1 (14/5) :=
    C981CompletionWallAdvance.point (owner p 4096) (side p 4096) (box p 4096) markL lG
      (foreign 4096 2 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ vHi)
      (foreign 4096 2 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ vDeep)
      (foreign 4096 2048 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ markN)
  have lSegment (y : ℝ) (lo : 113/50≤y) (hi : y≤14/5) : (owner p 4096).Inside 1 y :=
    vertical_segment _ _ _ _ _ lF lFar (by norm_num) lo hi
  have rFar : (owner p 16384).Inside 3 (14/5) := by
    have h := C981CompletionWallAdvance.point (pullX (owner p 16384)) (side p 16384)
      (container_transform (⟨false,true,false⟩ : Transform) (owner p 16384) (box p 16384))
      (by norm_num [inside_pullX]; exact markR)
      (by norm_num [inside_pullX]; exact rG)
      (by norm_num [inside_pullX]; exact (foreign 16384 8
        (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel) _ _ iF))
      (by norm_num [inside_pullX]; exact (foreign 16384 8
        (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel) _ _ iDeep))
      (by norm_num [inside_pullX]; exact (foreign 16384 1536
        (by cases k <;> decide +kernel) (by cases k <;> decide +kernel) (by decide +kernel) _ _ markW1))
    norm_num [inside_pullX] at h; exact h
  have eFar : (owner p 48).Inside 3 (18/5) := by
    let e := C981CompletionCharts.corner (pullX (owner p 48))
    have origin : e.Inside 0 0 := by
      norm_num [e,C981CompletionCharts.inside_corner,inside_pullX]
      exact cornerE
    have missingLeft : ¬e.Inside (-1/5) 0 := by
      norm_num [e,C981CompletionCharts.inside_corner,inside_pullX]
      exact foreign 48 16384 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ rFar
    have missingBelow : ¬e.Inside 0 (-37/50) := by
      norm_num [e,C981CompletionCharts.inside_corner,inside_pullX]
      exact foreign 48 32768 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ tG
    have h := C981CompletionCornerAdvance.point e (side p 48)
      (C981CompletionCharts.corner_wall _
        (container_transform (⟨false,true,false⟩ : Transform) (owner p 48) (box p 48)))
      origin (by simpa only [neg_div] using missingLeft)
      (by simpa only [neg_div] using missingBelow)
    norm_num [e,C981CompletionCharts.inside_corner,inside_pullX] at h
    exact h
  have eSegment (z : ℝ) (lo : 0≤z) (hi : z≤3/5) : (owner p 48).Inside 3 (3+z) :=
    vertical_segment _ _ _ _ _ cornerE eFar (by norm_num)
      (by linarith only [lo]) (by linarith only [hi])
  have tOrigin : (owner p 32768).Inside 2 3 := by
    let t := C981CompletionCharts.shiftedTop (owner p 32768)
    have north : t.Inside 0 (43/500) := by
      norm_num [t,C981CompletionCharts.inside_shiftedTop]
      exact markT
    have east : t.Inside (2/5) 0 := by
      norm_num [t,C981CompletionCharts.inside_shiftedTop]
      exact tF
    have avoid : ∀ z : ℝ, 0≤z → z≤3/5 → ¬t.Inside 1 z := by
      intro z lo hi own
      have h := (C981CompletionCharts.inside_shiftedTop _ _ _).mp own
      norm_num at h
      exact foreign 32768 48 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ (eSegment z lo hi) h
    have h := C981CompletionWallOrigin.point t (side p 32768)
      (C981CompletionCharts.shiftedTop_wall _ (box p 32768)) north east avoid
    norm_num [t,C981CompletionCharts.inside_shiftedTop] at h
    exact h
  have nSharp := NorthwestSharpPoint.point_original (owner p 2048) (side p 2048) markN nF nG
    (foreign 2048 1536 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ wF)
    (foreign 2048 32768 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ tOrigin)
    (foreign 2048 192 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ cornerK)
    (foreign 2048 32768 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ markT)
    (by
      intro z lo hi
      exact foreign 2048 4096 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
        (by decide +kernel) _ _ (lSegment z lo hi))
  have wNear := MergedInwardPoint.point_original (owner p 1536) (side p 1536) markW0 markW1 wF
    (foreign 1536 256 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ aP)
    (foreign 1536 8 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ iF)
    (foreign 1536 16384 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ markR)
    (foreign 1536 2048 (by cases k <;> decide +kernel) (by cases k <;> decide +kernel)
      (by decide +kernel) _ _ nSharp)
  exact apart (family k) p hf 256 1536 (by cases k <;> decide +kernel)
    (by cases k <;> decide +kernel) (by decide +kernel) _ _ ⟨aNear,wNear⟩

private theorem row48_checked :
    (RowIdentity.rowAt 87).originalId=48 ∧ (RowIdentity.rowAt 87).groups=family .c48 := by decide +kernel
private theorem row573_checked :
    (RowIdentity.rowAt 314).originalId=573 ∧ (RowIdentity.rowAt 314).groups=family .c573 := by decide +kernel
private theorem row574_checked :
    (RowIdentity.rowAt 315).originalId=574 ∧ (RowIdentity.rowAt 315).groups=family .c574 := by decide +kernel

theorem excludes48 : ExcludesCase 48 := by
  intro r hr he p hf
  exact family_impossible .c48 p
    (hf.trans (RowIdentity.family_at 87 48 (family .c48) row48_checked r hr he))
theorem excludes573 : ExcludesCase 573 := by
  intro r hr he p hf
  exact family_impossible .c573 p
    (hf.trans (RowIdentity.family_at 314 573 (family .c573) row573_checked r hr he))
theorem excludes574 : ExcludesCase 574 := by
  intro r hr he p hf
  exact family_impossible .c574 p
    (hf.trans (RowIdentity.family_at 315 574 (family .c574) row574_checked r hr he))

#print axioms excludes48
#print axioms excludes573
#print axioms excludes574
end
end N12Compact.CommonCases.C48Rows
