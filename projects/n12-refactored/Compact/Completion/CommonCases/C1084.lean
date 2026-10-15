import Compact.Completion.CommonCases.CentralPair
import Compact.Completion.CommonCases.OriginalOwners
import Compact.Completion.C981.WallAdvance
import Compact.Cases.MergedLower.Helpers
import Compact.Assembly.RowIdentity

/-! C1084's complete original owner entrance and continuous ending.
The only finite join has four central/right-wall alternatives. Both wall
segments belong strictly to their one actual owner, including endpoints. -/
namespace N12Compact.CommonCases.C1084
open S12 S12Pilot S12Completion OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

def family : Finset Nat :=
  {1,12,48,64,256,512,1024,2048,4096,8192,16384,32768}

private def southDomain : CertifiedDomain family :=
  ofCombined family combinedSpec7 combinedSpec7_checked (by decide +kernel) (by decide +kernel)
private def rightDomain : CertifiedDomain family :=
  ofCombined family combinedSpec20 combinedSpec20_checked (by decide +kernel) (by decide +kernel)
private def bottomDomain : CertifiedDomain family :=
  ofCombined family combinedSpec18 combinedSpec18_checked (by decide +kernel) (by decide +kernel)
private def topDomain : CertifiedDomain family :=
  ofCombined family combinedSpec22 combinedSpec22_checked (by decide +kernel) (by decide +kernel)
private def northDomain : CertifiedDomain family :=
  ofTransformedCombined family 1024 ⟨false,true,true⟩ (by decide +kernel)
    combinedSpec5 combinedSpec5_checked (by decide +kernel) (by decide +kernel)
    halfTurnPerm halfTurnPerm halfTurnF_points halfTurnG_points
    (by decide +kernel) (by decide +kernel) (MergedLower.halfturnedAllowed combinedSpec5)
    (fun x hx y hy hxy => MergedLower.halfturnedAllowed_mem combinedSpec5 x y hx hy hxy)

private def southChoices : List (Finset Nat) := [{4,16},{4,18},{8,16},{8,18}]
private def northChoices : List (Finset Nat) := [{5,16},{5,19},{9,16},{9,19}]
private def Pattern (a n r : Finset Nat) : Prop :=
  (a={4,16} ∧ n∈([{5,19},{9,19}] : List (Finset Nat)) ∧ r={8,18}) ∨
  (n={5,16} ∧ a∈([{4,18},{8,18}] : List (Finset Nat)) ∧ r={9,19})

private theorem south_filtered : ∀ a∈southDomain.allowed,
    Disjoint a ({6,15} : Finset Nat) → a∈southChoices := by decide +kernel
private theorem north_filtered : ∀ n∈northDomain.allowed,
    Disjoint n ({7,17} : Finset Nat) → n∈northChoices := by decide +kernel
private theorem patterns_checked : ∀ a∈southChoices, ∀ n∈northChoices,
    ∀ r∈rightDomain.allowed, Disjoint a n → Disjoint a r → Disjoint n r → Pattern a n r := by
  unfold Pattern
  decide +kernel

private theorem inside_seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed family p hf mask member P checked

private theorem inside_known (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (owned : Finset Nat)
    (he : auxiliaries p mask=owned) (P : ℚ×ℚ)
    (checked : P∈queryInsidePoints mask 2 owned) : (owner p mask).Inside P.1 P.2 :=
  known_point family p hf mask member owned he P checked

private theorem bottom_top (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    auxiliaries p 8192={6,15} ∧ auxiliaries p 32768={7,17} := by
  have sw0 : (owner p 1).Inside (28/25) 1 := by
    have h := inside_seed p hf 1 (by decide +kernel) (28/25,1) (by decide +kernel)
    norm_num at h; exact h
  have sw1 : (owner p 1).Inside (87/50) 1 := by
    have h := inside_seed p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have nw0 : (owner p 64).Inside (28/25) 3 := by
    have h := inside_seed p hf 64 (by decide +kernel) (28/25,3) (by decide +kernel)
    norm_num at h; exact h
  have nw1 : (owner p 64).Inside (87/50) 3 := by
    have h := inside_seed p hf 64 (by decide +kernel) (87/50,3) (by decide +kernel)
    norm_num at h; exact h
  have sw := horizontal_segment (owner p 1) (28/25) (87/50) 1 (8/5)
    sw0 sw1 (by norm_num) (by norm_num) (by norm_num)
  have nw := horizontal_segment (owner p 64) (28/25) (87/50) 3 (8/5)
    nw0 nw1 (by norm_num) (by norm_num) (by norm_num)
  constructor
  · have options := domain family bottomDomain p hf (by decide +kernel)
    change auxiliaries p 8192∈([{2,12},{6,15}] : List (Finset Nat)) at options
    simp only [List.mem_cons,List.not_mem_nil,or_false] at options
    rcases options with bad | good
    · have h := (auxiliary_exact p 8192 2 (by norm_num)).mpr (by rw [bad]; decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h
      exact (apart family p hf 8192 1 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨h,sw⟩).elim
    · exact good
  · have options := domain family topDomain p hf (by decide +kernel)
    change auxiliaries p 32768∈([{3,14},{7,17}] : List (Finset Nat)) at options
    simp only [List.mem_cons,List.not_mem_nil,or_false] at options
    rcases options with bad | good
    · have h := (auxiliary_exact p 32768 3 (by norm_num)).mpr (by rw [bad]; decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h
      exact (apart family p hf 32768 64 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨h,nw⟩).elim
    · exact good

private theorem central_pattern (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (bottom : auxiliaries p 8192={6,15}) (top : auxiliaries p 32768={7,17}) :
    Pattern (auxiliaries p 512) (auxiliaries p 1024) (auxiliaries p 16384) := by
  have south := domain family southDomain p hf (by decide +kernel)
  have north := domain family northDomain p hf (by decide +kernel)
  have right := domain family rightDomain p hf (by decide +kernel)
  have southBottom := auxiliary_disjoint family p hf 512 8192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [bottom] at southBottom
  have northTop := auxiliary_disjoint family p hf 1024 32768
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [top] at northTop
  exact patterns_checked _ (south_filtered _ south southBottom)
    _ (north_filtered _ north northTop) _ right
    (auxiliary_disjoint family p hf 512 1024 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (auxiliary_disjoint family p hf 512 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (auxiliary_disjoint family p hf 1024 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨bottomLabel,topLabel⟩ := bottom_top p hf
  have markSW : (owner p 256).Inside (33/20) (33/20) := by
    have h := inside_seed p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markSE : (owner p 512).Inside (47/20) (33/20) := by
    have h := inside_seed p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markNE : (owner p 1024).Inside (47/20) (47/20) := by
    have h := inside_seed p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markNW : (owner p 2048).Inside (33/20) (47/20) := by
    have h := inside_seed p hf 2048 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have bottomMarker : (owner p 8192).Inside 2 (457/500) := by
    have h := inside_seed p hf 8192 (by decide +kernel) (2,457/500) (by decide +kernel)
    norm_num at h; exact h
  have topMarker : (owner p 32768).Inside 2 (1543/500) := by
    have h := inside_seed p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have rightMarker : (owner p 16384).Inside (1543/500) 2 := by
    have h := inside_seed p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have bottomElbow : (owner p 8192).Inside (113/50) 1 := by
    have h := inside_known p hf 8192 (by decide +kernel) _ bottomLabel (113/50,1) (by decide +kernel)
    norm_num at h; exact h
  have bottomOuter : (owner p 8192).Inside (12/5) 1 := by
    have h := inside_known p hf 8192 (by decide +kernel) _ bottomLabel (12/5,1) (by decide +kernel)
    norm_num at h; exact h
  have topElbow : (owner p 32768).Inside (113/50) 3 := by
    have h := inside_known p hf 32768 (by decide +kernel) _ topLabel (113/50,3) (by decide +kernel)
    norm_num at h; exact h
  have topOuter : (owner p 32768).Inside (12/5) 3 := by
    have h := inside_known p hf 32768 (by decide +kernel) _ topLabel (12/5,3) (by decide +kernel)
    norm_num at h; exact h
  have swTip : (owner p 1).Inside (87/50) 1 := by
    have h := inside_seed p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have swSeed : (owner p 1).Inside (187/100) (19/25) := by
    have h := inside_seed p hf 1 (by decide +kernel) (187/100,19/25) (by decide +kernel)
    norm_num at h; exact h
  have nwTip : (owner p 64).Inside (87/50) 3 := by
    have h := inside_seed p hf 64 (by decide +kernel) (87/50,3) (by decide +kernel)
    norm_num at h; exact h
  have nwSeed : (owner p 64).Inside (187/100) (81/25) := by
    have h := inside_seed p hf 64 (by decide +kernel) (187/100,81/25) (by decide +kernel)
    norm_num at h; exact h
  have foreign (m n : Nat) (hm : m∈family) (hn : n∈family) (hne : m≠n)
      (x y : ℝ) (own : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun h => apart family p hf m n hm hn hne x y ⟨h,own⟩
  have bottomAdvance : (owner p 8192).Inside (14/5) 1 := by
    have h := C981CompletionWallAdvance.point (pullSwap (owner p 8192)) (side p 8192)
      (container_pullSwap _ (box p 8192))
      (by norm_num [inside_pullSwap]; exact bottomMarker)
      (by norm_num [inside_pullSwap]; exact bottomOuter)
      (by norm_num [inside_pullSwap]; exact (foreign 8192 1 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ swTip))
      (by norm_num [inside_pullSwap]; exact (foreign 8192 1 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ swSeed))
      (by norm_num [inside_pullSwap]; exact (foreign 8192 512 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markSE))
    simpa [inside_pullSwap] using h
  have topAdvance : (owner p 32768).Inside (14/5) 3 := by
    have h := C981CompletionWallAdvance.point (pullSwap (pullY (owner p 32768))) (side p 32768)
      (container_pullSwap _ (container_pullY _ (box p 32768)))
      (by norm_num [inside_pullSwap,inside_pullY]; exact topMarker)
      (by norm_num [inside_pullSwap,inside_pullY]; exact topOuter)
      (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign 32768 64 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ nwTip))
      (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign 32768 64 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ nwSeed))
      (by norm_num [inside_pullSwap,inside_pullY]; exact (foreign 32768 1024 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markNE))
    norm_num [inside_pullSwap,inside_pullY] at h
    exact h
  have lowerSegment (z : ℝ) (lo : 113/50≤z) (hi : z≤14/5) : (owner p 8192).Inside z 1 :=
    horizontal_segment _ _ _ _ _ bottomElbow bottomAdvance (by norm_num) lo hi
  have upperSegment (z : ℝ) (lo : 113/50≤z) (hi : z≤14/5) : (owner p 32768).Inside z 3 :=
    horizontal_segment _ _ _ _ _ topElbow topAdvance (by norm_num) lo hi
  have seCorner : (owner p 12).Inside 3 1 := by
    have h := inside_seed p hf 12 (by decide +kernel) (3,1) (by decide +kernel)
    norm_num at h; exact h
  have seCornerMarker : (owner p 12).Inside (1543/500) 1 := by
    have h := inside_seed p hf 12 (by decide +kernel) (1543/500,1) (by decide +kernel)
    norm_num at h; exact h
  have neCorner : (owner p 48).Inside 3 3 := by
    have h := inside_seed p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
    norm_num at h; exact h
  have neCornerMarker : (owner p 48).Inside (1543/500) 3 := by
    have h := inside_seed p hf 48 (by decide +kernel) (1543/500,3) (by decide +kernel)
    norm_num at h; exact h
  rcases central_pattern p hf bottomLabel topLabel with lower | upper
  · obtain ⟨aLabel,nOptions,_⟩ := lower
    have inwardA : (owner p 512).Inside 2 (87/50) := by
      have h := inside_known p hf 512 (by decide +kernel) _ aLabel (2,87/50) (by decide +kernel)
      norm_num at h; exact h
    have elbowA : (owner p 512).Inside (113/50) 2 := by
      have h := inside_known p hf 512 (by decide +kernel) _ aLabel (113/50,2) (by decide +kernel)
      norm_num at h; exact h
    have pairN : ((owner p 1024).Inside 2 (113/50) ∧ (owner p 1024).Inside 3 (12/5)) ∨
        ((owner p 1024).Inside 3 (113/50) ∧ (owner p 1024).Inside 3 (12/5)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at nOptions
      rcases nOptions with mixed | outward
      · left; constructor
        · have h := inside_known p hf 1024 (by decide +kernel) _ mixed (2,113/50) (by decide +kernel)
          norm_num at h; exact h
        · have h := inside_known p hf 1024 (by decide +kernel) _ mixed (3,12/5) (by decide +kernel)
          norm_num at h; exact h
      · right; constructor
        · have h := inside_known p hf 1024 (by decide +kernel) _ outward (3,113/50) (by decide +kernel)
          norm_num at h; exact h
        · have h := inside_known p hf 1024 (by decide +kernel) _ outward (3,12/5) (by decide +kernel)
          norm_num at h; exact h
    apply CentralPair.impossible (owner p 512) (owner p 1024) (side p 512) (side p 1024)
      markSE inwardA elbowA
      (foreign 512 256 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markSW)
      (foreign 512 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ bottomOuter)
      markNE pairN
      (foreign 1024 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ rightMarker)
      (foreign 1024 48 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ neCorner)
      (foreign 1024 48 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ neCornerMarker)
      (fun z lo hi => foreign 1024 32768 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ (upperSegment z lo hi))
      (apart family p hf 512 1024 (by decide +kernel) (by decide +kernel) (by decide +kernel))
  · obtain ⟨nLabel,aOptions,_⟩ := upper
    have inwardN : (owner p 1024).Inside 2 (113/50) := by
      have h := inside_known p hf 1024 (by decide +kernel) _ nLabel (2,113/50) (by decide +kernel)
      norm_num at h; exact h
    have elbowN : (owner p 1024).Inside (113/50) 2 := by
      have h := inside_known p hf 1024 (by decide +kernel) _ nLabel (113/50,2) (by decide +kernel)
      norm_num at h; exact h
    have pairA : ((pullY (owner p 512)).Inside 2 (113/50) ∧
        (pullY (owner p 512)).Inside 3 (12/5)) ∨
        ((pullY (owner p 512)).Inside 3 (113/50) ∧
          (pullY (owner p 512)).Inside 3 (12/5)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at aOptions
      rcases aOptions with mixed | outward
      · left; constructor
        · norm_num [inside_pullY]
          have h := inside_known p hf 512 (by decide +kernel) _ mixed (2,87/50) (by decide +kernel)
          norm_num at h; exact h
        · norm_num [inside_pullY]
          have h := inside_known p hf 512 (by decide +kernel) _ mixed (3,8/5) (by decide +kernel)
          norm_num at h; exact h
      · right; constructor
        · norm_num [inside_pullY]
          have h := inside_known p hf 512 (by decide +kernel) _ outward (3,87/50) (by decide +kernel)
          norm_num at h; exact h
        · norm_num [inside_pullY]
          have h := inside_known p hf 512 (by decide +kernel) _ outward (3,8/5) (by decide +kernel)
          norm_num at h; exact h
    apply CentralPair.impossible (pullY (owner p 1024)) (pullY (owner p 512))
      (side p 1024) (side p 512)
      (by norm_num [inside_pullY]; exact markNE)
      (by norm_num [inside_pullY]; exact inwardN)
      (by norm_num [inside_pullY]; exact elbowN)
      (by norm_num [inside_pullY]; exact (foreign 1024 2048 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markNW))
      (by norm_num [inside_pullY]; exact (foreign 1024 32768 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ topOuter))
      (by norm_num [inside_pullY]; exact markSE) pairA
      (by norm_num [inside_pullY]; exact (foreign 512 16384 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ rightMarker))
      (by norm_num [inside_pullY]; exact (foreign 512 12 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ seCorner))
      (by norm_num [inside_pullY]; exact (foreign 512 12 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ seCornerMarker))
    · intro z lo hi own
      exact foreign 512 8192 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ (lowerSegment z lo hi) (by norm_num [inside_pullY] at own; exact own)
    · intro x y both
      exact apart family p hf 1024 512 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨(inside_pullY _ _ _).mp both.1,(inside_pullY _ _ _).mp both.2⟩

private theorem row_checked :
    (RowIdentity.rowAt 568).originalId=1084 ∧ (RowIdentity.rowAt 568).groups=family := by
  decide +kernel

theorem excludes : ExcludesCase 1084 := by
  intro r hr he p hf
  exact family_impossible p (hf.trans (RowIdentity.family_at 568 1084 family row_checked r hr he))

#print axioms family_impossible
#print axioms excludes
end
end N12Compact.CommonCases.C1084
