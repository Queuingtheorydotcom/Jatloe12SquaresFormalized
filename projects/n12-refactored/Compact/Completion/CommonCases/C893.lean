import Compact.Completion.CommonCases.C893Point
import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.OriginalOwners
import Compact.Completion.C981.WallAdvance
import Compact.Completion.C981.Crosspoint
import Compact.Bridge.TransformedOwnerBudget
import Compact.Assembly.RowIdentity

namespace N12Compact.CommonCases.C893
open S12 S12Pilot S12Completion OriginalOwners RelaxedOwnerDomain
noncomputable section
set_option Elab.async false

def family : Finset Nat :=
  {1,2,12,16,192,512,1056,2304,4096,8192,16384,32768}

private def direct (w : CombinedSpec) (hw : w.Check)
    (first : Bounds family w.mask w.first.val 0)
    (second : Bounds family w.mask w.second.val 1) : CertifiedDomain family :=
  restrictByBudget family (ofCombined family w hw first second)
private def southwestDomain := direct combinedSpec1 combinedSpec1_checked
  (by decide +kernel) (by decide +kernel)
private def singletonDomain := direct combinedSpec4 combinedSpec4_checked
  (by decide +kernel) (by decide +kernel)
private def bottomDomain := direct combinedSpec19 combinedSpec19_checked
  (by decide +kernel) (by decide +kernel)
private def rightDomain := direct combinedSpec21 combinedSpec21_checked
  (by decide +kernel) (by decide +kernel)
private def southDomain := direct combinedSpec8 combinedSpec8_checked
  (by decide +kernel) (by decide +kernel)

private def swapFG : Fin 10 ≃ Fin 10 :=
  Equiv.ofBijective gInverseIndex (by decide +kernel)
private theorem swapFG_points (j : Fin 10) :
    (⟨true,false,false⟩ : Transform).applyRat ((auxPoints 0)[j.val]!) =
      (auxPoints 1)[(swapFG j).val]! := by fin_cases j <;> decide +kernel
private def northGDomain : OwnerBudget.HalfDomain family 1056 1 :=
  OwnerBudget.HalfDomain.ofTransformedSingletonSpec family 1056 1 0
    ⟨true,false,false⟩ (by decide +kernel) singleSpec36 singleSpec36_checked
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) swapFG swapFG_points [{7},{9}]
    (by intro j; fin_cases j <;> decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem singleton_sets :
    (∀ s∈southwestDomain.allowed,s=({2,12} : Finset Nat)) ∧
    (∀ s∈singletonDomain.allowed,s=({7,17} : Finset Nat)) := by decide +kernel
private theorem bottom_filtered : ∀ b∈bottomDomain.allowed,
    Disjoint b ({2,12} : Finset Nat) → b∈([{6,15},{4,6,15}] : List (Finset Nat)) := by
  decide +kernel
private theorem right_filtered : ∀ r∈rightDomain.allowed,
    Disjoint r ({6,15} : Finset Nat) → Disjoint r ({7,17} : Finset Nat) →
    19∉r → r∈([{8,18},{8,9,18}] : List (Finset Nat)) := by decide +kernel
private theorem south_filtered : ∀ a∈southDomain.allowed,
    Disjoint a ({6,15} : Finset Nat) → Disjoint a ({8,18} : Finset Nat) →
    ({4,16} : Finset Nat)⊆a := by decide +kernel

private theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (hm : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed family p hf mask hm P checked

private theorem north_upper (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 1056).Inside 3 (12/5) := by
  have hc := code family p hf 1056 (by decide +kernel)
  have options := northGDomain.sound p (ownerIndex p 1056) hf hc
  change natAuxOwners p 1 (ownerIndex p 1056)∈([{7},{9}] : List (Finset Nat)) at options
  simp only [List.mem_cons,List.not_mem_nil,or_false] at options
  rcases options with bad | good
  · have h := (nat_aux_exact p 1 (ownerIndex p 1056) 7 (by decide +kernel)).mpr
      (by rw [bad]; decide +kernel)
    norm_num [auxKind,auxPoints,fPoints,gPoints] at h
    have other : (owner p 16).Inside (113/50) 3 := by
      have k := seed_point p hf 16 (by decide +kernel) (113/50,3) (by decide +kernel)
      norm_num at k; exact k
    exact (apart family p hf 1056 16 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,other⟩).elim
  · have h := (nat_aux_exact p 1 (ownerIndex p 1056) 9 (by decide +kernel)).mpr
      (by rw [good]; decide +kernel)
    norm_num [auxKind,auxPoints,fPoints,gPoints] at h
    exact h

private theorem entrance (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    {6,15}⊆auxiliaries p 8192 ∧ {8,18}⊆auxiliaries p 16384 ∧
      {4,16}⊆auxiliaries p 512 ∧ (owner p 1056).Inside 3 (12/5) := by
  have sw := singleton_sets.1 _ (domain family southwestDomain p hf (by decide +kernel))
  have tr := singleton_sets.2 _ (domain family singletonDomain p hf (by decide +kernel))
  change auxiliaries p 1=({2,12} : Finset Nat) at sw
  change auxiliaries p 16=({7,17} : Finset Nat) at tr
  have bottomOptions := domain family bottomDomain p hf (by decide +kernel)
  have bottomApart := auxiliary_disjoint family p hf 8192 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [sw] at bottomApart
  have bottomOptions' := bottom_filtered _ bottomOptions bottomApart
  have bottom : ({6,15} : Finset Nat)⊆auxiliaries p 8192 := by
    have checked : ∀ b∈([{6,15},{4,6,15}] : List (Finset Nat)),({6,15} : Finset Nat)⊆b := by decide +kernel
    exact checked _ bottomOptions'
  have north := north_upper p hf
  have nineteen : 19∈auxiliaries p 1056 := by
    apply (auxiliary_exact p 1056 19 (by norm_num)).mp
    norm_num [auxPoints,fPoints,gPoints]
    exact north
  have rightNorth := auxiliary_disjoint family p hf 16384 1056
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have missingNineteen : 19∉auxiliaries p 16384 := fun h => Finset.disjoint_left.mp rightNorth h nineteen
  have rightBottom := auxiliary_disjoint family p hf 16384 8192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have rightBottom' : Disjoint (auxiliaries p 16384) ({6,15} : Finset Nat) :=
    rightBottom.mono_right bottom
  have rightSingleton := auxiliary_disjoint family p hf 16384 16
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [tr] at rightSingleton
  have rightOptions := right_filtered _ (domain family rightDomain p hf (by decide +kernel))
    rightBottom' rightSingleton missingNineteen
  have right : ({8,18} : Finset Nat)⊆auxiliaries p 16384 := by
    have checked : ∀ r∈([{8,18},{8,9,18}] : List (Finset Nat)),({8,18} : Finset Nat)⊆r := by decide +kernel
    exact checked _ rightOptions
  have southBottom := auxiliary_disjoint family p hf 512 8192
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have southRight := auxiliary_disjoint family p hf 512 16384
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have south := south_filtered _ (domain family southDomain p hf (by decide +kernel))
    (southBottom.mono_right bottom) (southRight.mono_right right)
  exact ⟨bottom,right,south,north⟩

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  obtain ⟨bottomAux,_,southAux,northUpper⟩ := entrance p hf
  have markerA : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed_point p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markerN : (owner p 1056).Inside (47/20) (47/20) := by
    have h := seed_point p hf 1056 (by decide +kernel) (47/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have cornerN : (owner p 1056).Inside (1543/500) 3 := by
    have h := seed_point p hf 1056 (by decide +kernel) (1543/500,3) (by decide +kernel)
    norm_num at h; exact h
  have markerSW : (owner p 2304).Inside (33/20) (33/20) := by
    have h := seed_point p hf 2304 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h; exact h
  have markerR : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed_point p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h; exact h
  have tip : (owner p 16).Inside (72/25) 3 := by
    have h := seed_point p hf 16 (by decide +kernel) (72/25,3) (by decide +kernel)
    norm_num at h; exact h
  have inwardA : (owner p 512).Inside 2 (87/50) := by
    have h := (auxiliary_exact p 512 4 (by norm_num)).mpr (southAux (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have elbowA : (owner p 512).Inside (113/50) 2 := by
    have h := (auxiliary_exact p 512 16 (by norm_num)).mpr (southAux (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have bottomOuter : (owner p 8192).Inside (12/5) 1 := by
    have h := (auxiliary_exact p 8192 6 (by norm_num)).mpr (bottomAux (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have bottomElbow : (owner p 8192).Inside (113/50) 1 := by
    have h := (auxiliary_exact p 8192 15 (by norm_num)).mpr (bottomAux (by decide +kernel))
    norm_num [auxPoints,fPoints,gPoints] at h; exact h
  have bottomMarker : (owner p 8192).Inside 2 (457/500) := by
    have h := seed_point p hf 8192 (by decide +kernel) (2,457/500) (by decide +kernel)
    norm_num at h; exact h
  have swTip : (owner p 1).Inside (87/50) 1 := by
    have h := seed_point p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h; exact h
  have swSeed : (owner p 1).Inside (187/100) (19/25) := by
    have h := seed_point p hf 1 (by decide +kernel) (187/100,19/25) (by decide +kernel)
    norm_num at h; exact h
  have foreign (m n : Nat) (hm : m∈family) (hn : n∈family) (hne : m≠n)
      (x y : ℝ) (own : (owner p n).Inside x y) : ¬(owner p m).Inside x y :=
    fun h => apart family p hf m n hm hn hne x y ⟨h,own⟩
  have missingSW := foreign 512 2304 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ markerSW
  have missingNE := foreign 512 1056 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ markerN
  have missingBottom := foreign 512 8192 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) _ _ bottomOuter
  have strong := InwardPoint.strong_original (owner p 512) (side p 512)
    markerA inwardA elbowA missingSW missingNE missingBottom
  have advance : (owner p 8192).Inside (14/5) 1 := by
    have h := C981CompletionWallAdvance.point (pullSwap (owner p 8192)) (side p 8192)
      (container_pullSwap _ (box p 8192))
      (by norm_num [inside_pullSwap]; exact bottomMarker)
      (by norm_num [inside_pullSwap]; exact bottomOuter)
      (by norm_num [inside_pullSwap]; exact (foreign 8192 1 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ swTip))
      (by norm_num [inside_pullSwap]; exact (foreign 8192 1 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ swSeed))
      (by norm_num [inside_pullSwap]; exact (foreign 8192 512 (by decide +kernel)
        (by decide +kernel) (by decide +kernel) _ _ markerA))
    simpa [inside_pullSwap] using h
  have bottomHalf : (owner p 8192).Inside (5/2) 1 :=
    horizontal_segment _ _ _ _ _ bottomElbow advance (by norm_num) (by norm_num) (by norm_num)
  have center : (owner p 512).Inside (5/2) 2 := by
    let t : Transform := ⟨true,false,true⟩
    have h := C981CompletionCrosspoint.point (t.pull (owner p 512)) (side p 512)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact elbowA)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact inwardA)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact markerA)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact missingSW)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact missingNE)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact missingBottom)
      (by norm_num [t,Transform.pull,inside_pullSwap,inside_pullY]; exact (foreign 512 8192
        (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ bottomHalf))
    norm_num [t,Transform.pull,inside_pullSwap,inside_pullY] at h
    exact h
  have points := C893Point.points_original (owner p 1056) (side p 1056) markerN northUpper cornerN
    (foreign 1056 512 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ elbowA)
    (foreign 1056 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ markerR)
    (foreign 1056 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ tip)
  rcases points with first | second
  · exact apart family p hf 512 1056 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨center,first⟩
  · exact apart family p hf 512 1056 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨strong,second⟩

private theorem row_checked :
    (RowIdentity.rowAt 480).originalId=893 ∧ (RowIdentity.rowAt 480).groups=family := by decide +kernel

theorem excludes : ExcludesCase 893 := by
  intro r hr he p hf
  exact family_impossible p (hf.trans (RowIdentity.family_at 480 893 family row_checked r hr he))

#print axioms family_impossible
#print axioms excludes
end
end N12Compact.CommonCases.C893
