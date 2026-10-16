import Compact.Completion.CommonCases.OriginalOwners
import Compact.Completion.C981.WallAdvance
import Compact.Completion.FiniteCases.MergedCornerPoint
import S12.DomainSpecData

/-! The compulsory C997 wall and merged-corner points come from its original
real packing. The G join retains the two-point allowances of all ordinary
owners until actual disjointness removes them. No catalogue hull is assumed. -/
namespace N12Compact.FiniteCases.C997Entrance
open S12 S12Pilot RelaxedOwnerDomain
open N12Compact.CommonCases.OriginalOwners
noncomputable section
set_option Elab.async false

def family : Finset Nat :=
  {1,2,12,48,256,512,1024,2240,4096,8192,16384,32768}

private def swDomain : OwnerBudget.HalfDomain family 1 1 :=
  ofSingle _ singleSpec3 singleSpec3_checked 1 (by decide +kernel) (by decide +kernel)
private def lowDomain : OwnerBudget.HalfDomain family 2 1 :=
  ofSingle _ singleSpec7 singleSpec7_checked 1 (by decide +kernel) (by decide +kernel)
private def centralDomain : OwnerBudget.HalfDomain family 256 1 :=
  ofSingle _ singleSpec23 singleSpec23_checked 1 (by decide +kernel) (by decide +kernel)
private def wallDomain : OwnerBudget.HalfDomain family 4096 1 :=
  ofSingle _ singleSpec58 singleSpec58_checked 1 (by decide +kernel) (by decide +kernel)

def G (p : NormalizedPacking) (mask : Nat) : Finset Nat :=
  natAuxOwners p 1 (ownerIndex p mask)

private theorem actual (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (d : OwnerBudget.HalfDomain family mask 1) :
    G p mask∈d.allowed := d.sound p _ hf (code _ p hf mask member)

private theorem separate (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n) :
    Disjoint (G p m) (G p n) := by
  apply nat_aux_disjoint
  intro same
  exact different ((code _ p hf m hm).symm.trans
    ((congrArg (markerCode p) same).trans (code _ p hf n hn)))

theorem wall_label (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    G p 4096={1} := by
  have sw : 2∈G p 1 := by
    have h := actual p hf 1 (by decide +kernel) swDomain
    have checked : ∀ s∈swDomain.allowed, 2∈s := by decide +kernel
    exact checked _ h
  have low : 0∈G p 2 := by
    have h := actual p hf 2 (by decide +kernel) lowDomain
    have checked : ∀ s∈lowDomain.allowed, 0∈s := by decide +kernel
    exact checked _ h
  have central : 3∈G p 256 := by
    have h := actual p hf 256 (by decide +kernel) centralDomain
    have no0 : 0∉G p 256 := fun h => Finset.disjoint_left.mp
      (separate p hf 256 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h low
    have no2 : 2∉G p 256 := fun h => Finset.disjoint_left.mp
      (separate p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h sw
    have checked : ∀ s∈centralDomain.allowed, 0∉s → 2∉s → 3∈s := by decide +kernel
    exact checked _ h no0 no2
  have h := actual p hf 4096 (by decide +kernel) wallDomain
  have no0 : 0∉G p 4096 := fun h => Finset.disjoint_left.mp
    (separate p hf 4096 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h low
  have no3 : 3∉G p 4096 := fun h => Finset.disjoint_left.mp
    (separate p hf 4096 256 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h central
  have checked : ∀ s∈wallDomain.allowed, 0∉s → 3∉s → s={1} := by decide +kernel
  exact checked _ h no0 no3

private theorem seed_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (member : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 :=
  seed _ p hf mask member P checked

theorem wall_upper (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 4096).Inside 1 (12/5) := by
  have h := (nat_aux_exact p 1 (ownerIndex p 4096) 1 (by decide +kernel)).mpr
    (show 1∈G p 4096 by rw [wall_label p hf]; decide +kernel)
  norm_num [auxKind,auxPoints,gPoints] at h
  exact h

theorem wall_far (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 4096).Inside 1 (14/5) := by
  apply C981CompletionWallAdvance.point (owner p 4096) (side p 4096) (box p 4096)
  · have h := seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
    norm_num at h; exact h
  · exact wall_upper p hf
  · intro own
    have h := seed_point p hf 2 (by decide +kernel) (1,87/50) (by decide +kernel)
    norm_num at h
    exact apart _ p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,h⟩
  · intro own
    have h := seed_point p hf 2 (by decide +kernel) (19/25,187/100) (by decide +kernel)
    norm_num at h
    exact apart _ p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,h⟩
  · intro own
    have h := seed_point p hf 2240 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact apart _ p hf 4096 2240 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,h⟩

theorem merged_near (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2240).Inside 1 (1457/500) := by
  apply MergedCornerPoint.upper_left (owner p 2240) (side p 2240)
  · have h := seed_point p hf 2240 (by decide +kernel) (457/500,3) (by decide +kernel)
    norm_num at h; exact h
  · have h := seed_point p hf 2240 (by decide +kernel) (1,1543/500) (by decide +kernel)
    norm_num at h; exact h
  · have h := seed_point p hf 2240 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  · intro own
    have h := seed_point p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)
    norm_num at h
    exact apart _ p hf 2240 32768 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨own,h⟩

/-- This compulsory F3 is supplied by the original wall's real G1 point,
through the existing all-angle four-point theorem, rather than a budget claim. -/
theorem merged_outward (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 2240).Inside (8/5) 3 := by
  have left : (owner p 2240).Inside (457/500) 3 := by
    have h := seed_point p hf 2240 (by decide +kernel) (457/500,3) (by decide +kernel)
    norm_num at h; exact h
  have central : (owner p 2240).Inside (33/20) (47/20) := by
    have h := seed_point p hf 2240 (by decide +kernel) (33/20,47/20) (by decide +kernel)
    norm_num at h; exact h
  have alternatives := fourDatum4.sound fourDatum4_checked (pullY (owner p 2240))
    (side p 2240) (by norm_num [fourDatum4,inside_pullY]; exact left)
    (by norm_num [fourDatum4,inside_pullY]; exact central)
  rcases alternatives with bad | good
  · norm_num [fourDatum4,inside_pullY] at bad
    exact False.elim (apart _ p hf 2240 4096 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨bad,wall_upper p hf⟩)
  · norm_num [fourDatum4,inside_pullY] at good
    exact good

#print axioms wall_label
#print axioms wall_far
#print axioms merged_near
#print axioms merged_outward
end
end N12Compact.FiniteCases.C997Entrance
