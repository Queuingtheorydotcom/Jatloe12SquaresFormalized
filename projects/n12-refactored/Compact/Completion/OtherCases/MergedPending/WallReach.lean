import Compact.Completion.OtherCases.MergedPending.Domains
import Compact.Completion.OtherCases.C1089.ContinuousBottom

/-! Genuine longer foreign bars for the three pending merged families.
Each advance uses its own ordinary far point, its own missing central
marker, and two strict points in one distinct actual singleton. The
C867 right wall has only the proved upper bar; no lower point is added.
Source only, uncompiled. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
set_option Elab.async false
noncomputable section

private theorem raw_left (W : OpenSquare) (side : 1<W.side) (box : InsideContainer W)
    (marker : W.Inside (457/500) 2) (far : W.Inside 1 (12/5))
    (singleton : ¬W.Inside 1 (87/50)) (seed : ¬W.Inside (19/25) (187/100))
    (central : ¬W.Inside (33/20) (47/20)) :
    51/25<centerY W ∧ W.Inside 1 (14/5) ∧
      ∀ y : ℝ,113/50≤y → y≤14/5 → W.Inside 1 y := by
  have result := Completion.OtherCases.C1089.ContinuousBottom.reach_of_far
    (pullSwap W) side (container_pullSwap W box)
    (by simpa only [inside_pullSwap] using marker)
    (by simpa only [inside_pullSwap] using far)
    (by simpa only [inside_pullSwap] using singleton)
    (by simpa only [inside_pullSwap] using seed)
    (by simpa only [inside_pullSwap] using central)
  simpa only [center_pullSwap_x,inside_pullSwap] using result

theorem left_reach (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) :
    51/25<centerY (owner p 4096) ∧
      ∀ y : ℝ,113/50≤y → y≤14/5 → (owner p 4096).Inside 1 y := by
  have member := common_member k 4096 (by decide)
  have two := common_member k 2 (by decide)
  have mark := seed _ p hf 4096 member (457/500,2) (by decide +kernel)
  have far := (auxiliary_exact p 4096 11 (by norm_num)).mpr (common_labels k p hf).left.2
  have short := singleton_left _ p hf two (87/50) (by norm_num) le_rfl
  have extra := seed _ p hf 2 two (19/25,187/100) (by decide +kernel)
  have central := missing_marker _ p hf 4096 member 11 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at mark far extra central
  have apart := CommonCases.OriginalOwners.apart _ p hf 4096 2 member two (by decide)
  have result := raw_left _ (side p 4096) (box p 4096) mark far
    (fun own => apart _ _ ⟨own,short⟩) (fun own => apart _ _ ⟨own,extra⟩) central
  exact ⟨result.1,result.2.2⟩

theorem bottom_reach (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) :
    51/25<centerX (owner p 8192) ∧
      ∀ x : ℝ,113/50≤x → x≤14/5 → (owner p 8192).Inside x 1 := by
  have member := common_member k 8192 (by decide)
  have one := common_member k 1 (by decide)
  have mark := seed _ p hf 8192 member (2,457/500) (by decide +kernel)
  have far := (auxiliary_exact p 8192 6 (by norm_num)).mpr (common_labels k p hf).bottom.1
  have short := singleton_bottom _ p hf one (87/50) (by norm_num) le_rfl
  have extra := seed _ p hf 1 one (187/100,19/25) (by decide +kernel)
  have central := missing_marker _ p hf 8192 member 9 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at mark far extra central
  have apart := CommonCases.OriginalOwners.apart _ p hf 8192 1 member one (by decide)
  have result := Completion.OtherCases.C1089.ContinuousBottom.reach_of_far
    _ (side p 8192) (box p 8192) mark far
    (fun own => apart _ _ ⟨own,short⟩) (fun own => apart _ _ ⟨own,extra⟩) central
  exact ⟨result.1,result.2.2⟩

theorem top_reach (k : Case) (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family k) :
    centerX (owner p 32768)<49/25 ∧
      ∀ x : ℝ,6/5≤x → x≤87/50 → (owner p 32768).Inside x 3 := by
  have member := common_member k 32768 (by decide)
  have sixteen := common_member k 16 (by decide)
  let W := owner p 32768
  let Q := pullY (pullX W)
  have actual (x y : ℝ) : Q.Inside x y ↔ W.Inside (4-x) (4-y) := by
    simp only [Q,inside_pullY,inside_pullX]
  have mark := seed _ p hf 32768 member (2,1543/500) (by decide +kernel)
  have far := (auxiliary_exact p 32768 3 (by norm_num)).mpr (common_labels k p hf).top.1
  have short := singleton_top _ p hf sixteen (113/50) le_rfl (by norm_num)
  have extra := seed _ p hf 16 sixteen (213/100,81/25) (by decide +kernel)
  have central := missing_marker _ p hf 32768 member 11 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at mark far extra central
  have apart := CommonCases.OriginalOwners.apart _ p hf 32768 16 member sixteen (by decide)
  have result := Completion.OtherCases.C1089.ContinuousBottom.reach_of_far Q (side p 32768)
    (container_pullY _ (container_pullX _ (box p 32768)))
    (by rw [actual]; norm_num; exact mark)
    (by rw [actual]; norm_num; exact far)
    (by rw [actual]; norm_num; exact fun own => apart _ _ ⟨own,short⟩)
    (by rw [actual]; norm_num; exact fun own => apart _ _ ⟨own,extra⟩)
    (by rw [actual]; norm_num; exact central)
  constructor
  · have sign := result.1
    simp only [Q,center_pullY_x,center_pullX_x] at sign
    linarith only [sign]
  · intro x low high
    have point := (actual _ _).mp (result.2.2 (4-x)
      (by linarith only [high]) (by linarith only [low]))
    convert point using 1 <;> ring

theorem c700_right_reach (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) :
    centerY (owner p 16384)<49/25 ∧
      ∀ y : ℝ,6/5≤y → y≤87/50 → (owner p 16384).Inside 3 y := by
  let W := owner p 16384
  let Q := pullY (pullX W)
  have actual (x y : ℝ) : Q.Inside x y ↔ W.Inside (4-x) (4-y) := by
    simp only [Q,inside_pullY,inside_pullX]
  have mark := seed _ p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
  have far := (auxiliary_exact p 16384 18 (by norm_num)).mpr (c700_right_labels p hf).2
  have short := c700_right_singleton p hf (113/50) le_rfl (by norm_num)
  have extra := seed _ p hf 32 (by decide +kernel) (81/25,213/100) (by decide +kernel)
  have central := missing_marker _ p hf 16384 (by decide +kernel) 9 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at mark far extra central
  have apart := CommonCases.OriginalOwners.apart _ p hf 16384 32
    (by decide +kernel) (by decide +kernel) (by decide)
  have result := raw_left Q (side p 16384)
    (container_pullY _ (container_pullX _ (box p 16384)))
    (by rw [actual]; norm_num; exact mark)
    (by rw [actual]; norm_num; exact far)
    (by rw [actual]; norm_num; exact fun own => apart _ _ ⟨own,short⟩)
    (by rw [actual]; norm_num; exact fun own => apart _ _ ⟨own,extra⟩)
    (by rw [actual]; norm_num; exact central)
  constructor
  · have sign := result.1
    simp only [Q,center_pullY_y,center_pullX_y] at sign
    linarith only [sign]
  · intro y low high
    have point := (actual _ _).mp (result.2.2 (4-y)
      (by linarith only [high]) (by linarith only [low]))
    convert point using 1 <;> ring

/-- C867's right center is above two, from the actual foreign F8 in
southeast512. Its strict upper bar never supplies that foreign point. -/
theorem c867_right_upper (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c867) :
    21/10<centerY (owner p 16384) ∧
      ∀ y : ℝ,111/50≤y → y≤12/5 → (owner p 16384).Inside 3 y := by
  let W := owner p 16384
  let Q := pullX W
  have mark := seed _ p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
  have far := (auxiliary_exact p 16384 19 (by norm_num)).mpr (c867_right_labels p hf).2
  have lower := (auxiliary_exact p 512 8 (by norm_num)).mpr
    (southeast_lower .c867 p hf (by decide +kernel))
  have central := missing_marker _ p hf 16384 (by decide +kernel) 10 (by decide +kernel)
  norm_num [auxPoints,fPoints,gPoints,S12.marker] at mark far lower central
  have absent : ¬W.Inside 3 (87/50) := fun own =>
    apart _ p hf 16384 512 (by decide +kernel) (by decide +kernel) (by decide) _ _ ⟨own,lower⟩
  have high := WallLowerCenterBarrier.center_above Q (side p 16384)
    (container_pullX _ (box p 16384))
    (by norm_num only [Q,inside_pullX]; exact mark)
    (by norm_num only [Q,inside_pullX]; exact far)
    (by norm_num only [Q,inside_pullX]; exact absent)
    (by norm_num only [Q,inside_pullX]; exact central)
  have first := WallSignChord.chord Q (side p 16384)
    (fun x y own => (container_pullX _ (box p 16384) x y own).1)
    (by norm_num only [Q,inside_pullX]; exact mark)
    (by norm_num only [Q,inside_pullX]; exact central)
    (by linarith only [high]) (111/50) le_rfl (by norm_num)
  norm_num only [Q,inside_pullX] at first
  refine ⟨by simpa only [Q,center_pullX_y] using high,?_⟩
  intro y low upper
  exact vertical_segment _ _ _ _ _ first far (by norm_num) low upper

end
#print axioms bottom_reach
#print axioms top_reach
#print axioms c700_right_reach
#print axioms c867_right_upper
end N12Compact.MergedPending
