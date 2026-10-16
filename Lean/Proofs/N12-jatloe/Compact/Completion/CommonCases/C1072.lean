import Compact.Completion.CommonCases.CentralPair
import Compact.Completion.CommonCases.StrongBarPoint
import Compact.Completion.CommonCases.OriginalOwners
import Compact.Completion.C981.WallAdvance
import Compact.Completion.C1092.MixedSpan
import Compact.Assembly.RowIdentity

/-! Original C1072, retaining its missing southwest corner. The four
central/left-wall alternatives have one common top-wall advance. -/
namespace N12Compact.CommonCases.C1072
open S12 S12Pilot S12Completion OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false
set_option maxRecDepth 10000

def family : Finset Nat := {1,12,16,192,256,512,1024,2048,4096,8192,16384,32768}
private def southDomain : CertifiedDomain family :=
  ofCombined family combinedSpec5 combinedSpec5_checked (by decide +kernel) (by decide +kernel)
private def northDomain : CertifiedDomain family :=
  ofCombined family combinedSpec12 combinedSpec12_checked (by decide +kernel) (by decide +kernel)
private def leftDomain : CertifiedDomain family :=
  ofCombined family combinedSpec16 combinedSpec16_checked (by decide +kernel) (by decide +kernel)
private def topDomain : CertifiedDomain family :=
  ofCombined family combinedSpec22 combinedSpec22_checked (by decide +kernel) (by decide +kernel)
private def southwestDomain : CertifiedDomain family :=
  ofCombined family combinedSpec0 combinedSpec0_checked (by decide +kernel) (by decide +kernel)

private def Pattern (a n : Finset Nat) : Prop :=
  (a={4,13} ∧ n∈([{1,11},{5,11}] : List (Finset Nat))) ∨
  (n={5,13} ∧ a∈([{0,10},{4,10}] : List (Finset Nat)))
private theorem patterns_checked : ∀ a∈southDomain.allowed, ∀ n∈northDomain.allowed,
    ∀ l∈leftDomain.allowed, Disjoint a ({2,12} : Finset Nat) →
    Disjoint n ({3,14} : Finset Nat) → Disjoint a n → Disjoint a l → Disjoint n l →
    Pattern a n := by unfold Pattern; decide +kernel

private theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (hm : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed family p hf mask hm P checked
private theorem known (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (hm : mask∈family) (owned : Finset Nat) (equal : auxiliaries p mask=owned)
    (P : ℚ×ℚ) (checked : P∈queryInsidePoints mask 2 owned) :
    (owner p mask).Inside P.1 P.2 := known_point family p hf mask hm owned equal P checked

private theorem entrance (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    auxiliaries p 32768={3,14} ∧ Pattern (auxiliaries p 256) (auxiliaries p 2048) := by
  have singleton : (owner p 16).Inside (12/5) 3 := by
    have a : (owner p 16).Inside (113/50) 3 := by
      have h := seed_point p hf 16 (by decide +kernel) (113/50,3) (by decide +kernel)
      norm_num at h; exact h
    have b : (owner p 16).Inside (72/25) 3 := by
      have h := seed_point p hf 16 (by decide +kernel) (72/25,3) (by decide +kernel)
      norm_num at h; exact h
    exact horizontal_segment _ _ _ _ _ a b (by norm_num) (by norm_num) (by norm_num)
  have options := domain family topDomain p hf (by decide +kernel)
  change auxiliaries p 32768∈([{3,14},{7,17}] : List (Finset Nat)) at options
  simp only [List.mem_cons,List.not_mem_nil,or_false] at options
  have top : auxiliaries p 32768={3,14} := by
    rcases options with good | bad
    · exact good
    · have h := (auxiliary_exact p 32768 7 (by norm_num)).mpr (by rw [bad]; decide +kernel)
      norm_num [auxPoints,fPoints,gPoints] at h
      exact (apart family p hf 32768 16 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨h,singleton⟩).elim
  have southwest : auxiliaries p 1={2,12} := by
    have h := domain family southwestDomain p hf (by decide +kernel)
    change auxiliaries p 1∈([{2,12}] : List (Finset Nat)) at h
    simpa only [List.mem_singleton] using h
  have aBottom := auxiliary_disjoint family p hf 256 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have nTop := auxiliary_disjoint family p hf 2048 32768
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [southwest] at aBottom
  rw [top] at nTop
  refine ⟨top,?_⟩
  exact patterns_checked _ (domain family southDomain p hf (by decide +kernel))
    _ (domain family northDomain p hf (by decide +kernel))
    _ (domain family leftDomain p hf (by decide +kernel)) aBottom nTop
    (auxiliary_disjoint family p hf 256 2048 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (auxiliary_disjoint family p hf 256 4096 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (auxiliary_disjoint family p hf 2048 4096 (by decide +kernel) (by decide +kernel) (by decide +kernel))

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨topLabel,pattern⟩ := entrance p hf
  have markA : (owner p 256).Inside (33/20) (33/20) := by
    have h := seed_point p hf 256 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markN : (owner p 2048).Inside (33/20) (47/20) := by
    have h := seed_point p hf 2048 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markSE : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markNE : (owner p 1024).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1024 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have markL : (owner p 4096).Inside (457/500) 2 := by
    have h := seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  have topMarker : (owner p 32768).Inside 2 (1543/500) := by
    have h := seed_point p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h; exact h
  have topElbow : (owner p 32768).Inside (87/50) 3 := by
    have h := known p hf 32768 (by decide +kernel) _ topLabel (87/50,3) (by decide +kernel)
    norm_num at h; exact h
  have topOuter : (owner p 32768).Inside (8/5) 3 := by
    have h := known p hf 32768 (by decide +kernel) _ topLabel (8/5,3) (by decide +kernel)
    norm_num at h; exact h
  have trTip : (owner p 16).Inside (113/50) 3 := by
    have h := seed_point p hf 16 (by decide +kernel) (113/50,3) (by decide +kernel)
    norm_num at h; exact h
  have trSeed : (owner p 16).Inside (213/100) (81/25) := by
    have h := seed_point p hf 16 (by decide +kernel) (213/100,81/25) (by decide +kernel)
    norm_num at h; exact h
  have bottomLo : (owner p 1).Inside (28/25) 1 := by
    have h := seed_point p hf 1 (by decide +kernel) (28/25,1) (by decide +kernel)
    norm_num at h; exact h
  have bottomHi : (owner p 1).Inside (87/50) 1 := by
    have h := seed_point p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have bottomSegment (x : ℝ) (lo : 28/25≤x) (hi : x≤87/50) : (owner p 1).Inside x 1 :=
    horizontal_segment _ _ _ _ _ bottomLo bottomHi (by norm_num) lo hi
  have corner : (owner p 192).Inside 1 3 := by
    have h := seed_point p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
    norm_num at h; exact h
  have cornerMarker : (owner p 192).Inside (457/500) 3 := by
    have h := seed_point p hf 192 (by decide +kernel) (457/500,3) (by decide +kernel)
    norm_num at h; exact h
  have foreign (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n)
      (x y : ℝ) (point : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun own => apart family p hf m n hm hn different _ _ ⟨own,point⟩
  have topAdvance : (owner p 32768).Inside (6/5) 3 := by
    let t : Transform := ⟨true,true,true⟩
    have h := C981CompletionWallAdvance.point (t.pull (owner p 32768)) (side p 32768)
      (container_transform t _ (box p 32768))
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact topMarker)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]; exact topOuter)
      (by
        norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
        exact foreign 32768 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ trTip)
      (by
        norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
        exact foreign 32768 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ trSeed)
      (by
        norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY]
        exact foreign 32768 2048 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markN)
    norm_num [t,Transform.pull,inside_pullSwap,inside_pullX,inside_pullY] at h
    exact h
  have topSegment (x : ℝ) (lo : 6/5≤x) (hi : x≤87/50) : (owner p 32768).Inside x 3 :=
    horizontal_segment _ _ _ _ _ topAdvance topElbow (by norm_num) lo hi
  rcases pattern with lower | upper
  · obtain ⟨aLabel,nOptions⟩ := lower
    have inwardA : (owner p 256).Inside 2 (87/50) := by
      have h := known p hf 256 (by decide +kernel) _ aLabel (2,87/50) (by decide +kernel)
      norm_num at h; exact h
    have elbowA : (owner p 256).Inside (87/50) 2 := by
      have h := known p hf 256 (by decide +kernel) _ aLabel (87/50,2) (by decide +kernel)
      norm_num at h; exact h
    have pairN : ((pullX (owner p 2048)).Inside 2 (113/50) ∧
        (pullX (owner p 2048)).Inside 3 (12/5)) ∨
        ((pullX (owner p 2048)).Inside 3 (113/50) ∧ (pullX (owner p 2048)).Inside 3 (12/5)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at nOptions
      rcases nOptions with outward | mixed
      · right; constructor
        · norm_num [inside_pullX]
          have h := known p hf 2048 (by decide +kernel) _ outward (1,113/50) (by decide +kernel)
          norm_num at h; exact h
        · norm_num [inside_pullX]
          have h := known p hf 2048 (by decide +kernel) _ outward (1,12/5) (by decide +kernel)
          norm_num at h; exact h
      · left; constructor
        · norm_num [inside_pullX]
          have h := known p hf 2048 (by decide +kernel) _ mixed (2,113/50) (by decide +kernel)
          norm_num at h; exact h
        · norm_num [inside_pullX]
          have h := known p hf 2048 (by decide +kernel) _ mixed (1,12/5) (by decide +kernel)
          norm_num at h; exact h
    apply CentralPair.impossible (pullX (owner p 256)) (pullX (owner p 2048))
      (side p 256) (side p 2048)
      (by norm_num [inside_pullX]; exact markA)
      (by norm_num [inside_pullX]; exact inwardA)
      (by norm_num [inside_pullX]; exact elbowA)
      (by norm_num [inside_pullX]; exact (foreign 256 512 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markSE))
      (by norm_num [inside_pullX]; exact (foreign 256 1 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ (bottomSegment (8/5) (by norm_num) (by norm_num))))
      (by norm_num [inside_pullX]; exact markN) pairN
      (by norm_num [inside_pullX]; exact (foreign 2048 4096 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markL))
      (by norm_num [inside_pullX]; exact (foreign 2048 192 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ corner))
      (by norm_num [inside_pullX]; exact (foreign 2048 192 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ cornerMarker))
    · intro x lo hi own
      exact foreign 2048 32768 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
        (topSegment (4-x) (by linarith only [hi]) (by linarith only [lo]))
        ((inside_pullX _ _ _).mp own)
    · intro x y own
      exact apart family p hf 256 2048 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨(inside_pullX _ _ _).mp own.1,(inside_pullX _ _ _).mp own.2⟩
  · obtain ⟨nLabel,aOptions⟩ := upper
    have inwardN : (owner p 2048).Inside 2 (113/50) := by
      have h := known p hf 2048 (by decide +kernel) _ nLabel (2,113/50) (by decide +kernel)
      norm_num at h; exact h
    have elbowN : (owner p 2048).Inside (87/50) 2 := by
      have h := known p hf 2048 (by decide +kernel) _ nLabel (87/50,2) (by decide +kernel)
      norm_num at h; exact h
    have inwardPoint := InwardPoint.point_original (pullY (pullX (owner p 2048))) (side p 2048)
      (by norm_num [inside_pullX,inside_pullY]; exact markN)
      (by norm_num [inside_pullX,inside_pullY]; exact inwardN)
      (by norm_num [inside_pullX,inside_pullY]; exact elbowN)
      (by norm_num [inside_pullX,inside_pullY]; exact (foreign 2048 1024 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markNE))
      (by norm_num [inside_pullX,inside_pullY]; exact (foreign 2048 256 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markA))
      (by norm_num [inside_pullX,inside_pullY]; exact (foreign 2048 32768 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ topOuter))
    simp only [List.mem_cons,List.not_mem_nil,or_false] at aOptions
    rcases aOptions with outward | mixed
    · have outwardA : (owner p 256).Inside 1 (87/50) := by
        have h := known p hf 256 (by decide +kernel) _ outward (1,87/50) (by decide +kernel)
        norm_num at h; exact h
      have upperA : (owner p 256).Inside 1 (8/5) := by
        have h := known p hf 256 (by decide +kernel) _ outward (1,8/5) (by decide +kernel)
        norm_num at h; exact h
      have missingH : ¬(owner p 256).Inside (457/500) 1 := by
        have h := missing_marker family p hf 256 (by decide +kernel) 1 (by decide +kernel)
        norm_num [marker] at h; exact h
      have outwardPoint := StrongBarPoint.point_original (pullY (pullX (owner p 256))) (side p 256)
        (by norm_num [inside_pullX,inside_pullY]; exact markA)
        (by norm_num [inside_pullX,inside_pullY]; exact outwardA)
        (by norm_num [inside_pullX,inside_pullY]; exact upperA)
        (by norm_num [inside_pullX,inside_pullY]; exact (foreign 256 2048 (by decide +kernel)
          (by decide +kernel) (by decide +kernel) _ _ elbowN))
        (by norm_num [inside_pullX,inside_pullY]; exact (foreign 256 4096 (by decide +kernel)
          (by decide +kernel) (by decide +kernel) _ _ markL))
        (by norm_num [inside_pullX,inside_pullY]; exact missingH)
        (by
          intro x lo hi own
          exact foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
            (bottomSegment (4-x) (by linarith only [hi]) (by linarith only [lo]))
            (by norm_num [inside_pullX,inside_pullY] at own; exact own))
      norm_num [inside_pullX,inside_pullY] at inwardPoint outwardPoint
      exact apart family p hf 256 2048 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        _ _ ⟨outwardPoint,inwardPoint⟩
    · apply C1092MixedSpan.impossible (pullX (owner p 256)) (side p 256)
      · norm_num [inside_pullX]
        have h := known p hf 256 (by decide +kernel) _ mixed (2,87/50) (by decide +kernel)
        norm_num at h; exact h
      · norm_num [inside_pullX]
        have h := known p hf 256 (by decide +kernel) _ mixed (1,8/5) (by decide +kernel)
        norm_num at h; exact h
      · norm_num [inside_pullX]
        exact foreign 256 2048 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ elbowN
      · norm_num [inside_pullX]
        intro own
        have member := (auxiliary_exact p 256 0 (by norm_num)).mp
          (by norm_num [auxPoints,fPoints,gPoints]; exact own)
        rw [mixed] at member
        exact (by decide +kernel : 0∉({4,10} : Finset Nat)) member
      · norm_num [inside_pullX]
        exact foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ bottomHi
      · norm_num [inside_pullX]
        exact foreign 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _
          (bottomSegment (8/5) (by norm_num) (by norm_num))

private theorem row_checked :
    (RowIdentity.rowAt 556).originalId=1072 ∧ (RowIdentity.rowAt 556).groups=family := by decide +kernel
theorem excludes : ExcludesCase 1072 := by
  intro r hr he p hf
  exact family_impossible p (hf.trans (RowIdentity.family_at 556 1072 family row_checked r hr he))

#print axioms family_impossible
#print axioms excludes
end
end N12Compact.CommonCases.C1072
