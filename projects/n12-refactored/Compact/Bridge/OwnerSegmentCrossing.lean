import S12.CertifiedDomain
import S12.Convex

/-! Small exact certificates excluding two actual owners whose interior
segments intersect. Rational equality is checked separately from the original
marker/auxiliary membership. No sampled hull or separating-axis assumption is
used: strict convexity places the same point inside both original squares. -/
namespace N12Compact.OwnerSegmentCrossing
open S12 S12Pilot

structure Data where
  firstMask : Nat
  secondMask : Nat
  firstOwned : Finset Nat
  secondOwned : Finset Nat
  firstStart : ℚ × ℚ
  firstEnd : ℚ × ℚ
  secondStart : ℚ × ℚ
  secondEnd : ℚ × ℚ
  firstWeight : ℚ
  secondWeight : ℚ

def Data.InputCheck (d : Data) : Prop :=
  d.firstMask ≠ d.secondMask ∧
  d.firstStart ∈ queryInsidePoints d.firstMask 2 d.firstOwned ∧
  d.firstEnd ∈ queryInsidePoints d.firstMask 2 d.firstOwned ∧
  d.secondStart ∈ queryInsidePoints d.secondMask 2 d.secondOwned ∧
  d.secondEnd ∈ queryInsidePoints d.secondMask 2 d.secondOwned

instance (d : Data) : Decidable d.InputCheck :=
  inferInstanceAs (Decidable (_ ∧ _))

def Data.CrossCheck (d : Data) : Prop :=
  0 ≤ d.firstWeight ∧ d.firstWeight ≤ 1 ∧
  0 ≤ d.secondWeight ∧ d.secondWeight ≤ 1 ∧
  (1-d.firstWeight)*d.firstStart.1+d.firstWeight*d.firstEnd.1 =
    (1-d.secondWeight)*d.secondStart.1+d.secondWeight*d.secondEnd.1 ∧
  (1-d.firstWeight)*d.firstStart.2+d.firstWeight*d.firstEnd.2 =
    (1-d.secondWeight)*d.secondStart.2+d.secondWeight*d.secondEnd.2

theorem impossible (d : Data) (hd : d.InputCheck) (hx : d.CrossCheck)
    (family : Finset Nat) (hm : d.firstMask ∈ family) (hn : d.secondMask ∈ family)
    (p : NormalizedPacking) (hf : codedMarkerFamily p = family)
    (first : natCombinedOwners p (ownerIndex p d.firstMask) = d.firstOwned)
    (second : natCombinedOwners p (ownerIndex p d.secondMask) = d.secondOwned) : False := by
  classical
  obtain ⟨hne, hf0, hf1, hs0, hs1⟩ := hd
  obtain ⟨ht0, ht1, hu0, hu1, heX, heY⟩ := hx
  have inside (mask : Nat) (owned : Finset Nat) (hmask : mask ∈ family)
      (howned : natCombinedOwners p (ownerIndex p mask) = owned)
      (P : ℚ × ℚ) (hP : P ∈ queryInsidePoints mask 2 owned) :
      (p.square (ownerIndex p mask)).Inside P.1 P.2 := by
    have hc := ownerIndex_spec p mask (by rw [hf]; exact hmask)
    have ha := nat_combined_exact p (ownerIndex p mask)
    rw [howned] at ha
    exact query_inside_sound mask 2 owned _
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained _)
      (by simpa only [hc] using coded_exact p (ownerIndex p mask)) ha P hP
  have firstSegment := inside_segment (p.square (ownerIndex p d.firstMask))
    d.firstStart.1 d.firstStart.2 d.firstEnd.1 d.firstEnd.2 d.firstWeight
    (inside _ _ hm first _ hf0) (inside _ _ hm first _ hf1)
    (by exact_mod_cast ht0) (by exact_mod_cast ht1)
  have secondSegment := inside_segment (p.square (ownerIndex p d.secondMask))
    d.secondStart.1 d.secondStart.2 d.secondEnd.1 d.secondEnd.2 d.secondWeight
    (inside _ _ hn second _ hs0) (inside _ _ hn second _ hs1)
    (by exact_mod_cast hu0) (by exact_mod_cast hu1)
  have hx' : (1-(d.firstWeight : ℝ))*(d.firstStart.1 : ℝ)+
      (d.firstWeight : ℝ)*(d.firstEnd.1 : ℝ) =
      (1-(d.secondWeight : ℝ))*(d.secondStart.1 : ℝ)+
      (d.secondWeight : ℝ)*(d.secondEnd.1 : ℝ) := by exact_mod_cast heX
  have hy' : (1-(d.firstWeight : ℝ))*(d.firstStart.2 : ℝ)+
      (d.firstWeight : ℝ)*(d.firstEnd.2 : ℝ) =
      (1-(d.secondWeight : ℝ))*(d.secondStart.2 : ℝ)+
      (d.secondWeight : ℝ)*(d.secondEnd.2 : ℝ) := by exact_mod_cast heY
  rw [hx', hy'] at firstSegment
  have hc0 := ownerIndex_spec p d.firstMask (by rw [hf]; exact hm)
  have hc1 := ownerIndex_spec p d.secondMask (by rw [hf]; exact hn)
  exact p.disjoint (ownerIndex p d.firstMask) (ownerIndex p d.secondMask)
    (fun he => hne (hc0.symm.trans ((congrArg (markerCode p) he).trans hc1)))
    _ _ ⟨firstSegment, secondSegment⟩

#print axioms impossible
end N12Compact.OwnerSegmentCrossing
