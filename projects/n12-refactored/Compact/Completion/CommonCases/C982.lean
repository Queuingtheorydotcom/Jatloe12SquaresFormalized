import Compact.Completion.CommonCases.C982Obstruction
import Compact.Geometry.C982Merged
import Compact.Assembly.RowIdentity
import S12.Seeds

/-! The complete original C982 contract. Only original marker signatures,
the kernel proved singleton/corner seeds, and the two continuous geometric
lemmas are needed. The optional auxiliary-label tightening is unnecessary. -/
namespace N12Compact.CommonCases.C982
open S12 S12Pilot S12Completion
set_option Elab.async false

def family : Finset Nat :=
  {1,2,12,48,192,512,1024,2048,4096,8448,16384,32768}

private noncomputable def owner (p : NormalizedPacking) (mask : Nat) : OpenSquare :=
  p.square (ownerIndex p mask)

private theorem owner_code (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (hm : mask∈family) : markerCode p (ownerIndex p mask)=mask :=
  ownerIndex_spec p mask (by rw [hf]; exact hm)

private theorem side (p : NormalizedPacking) (mask : Nat) : 1 < (owner p mask).side := by
  change 1 < (p.square (ownerIndex p mask)).side
  rw [p.congruent]
  exact p.side_gt_one

private theorem seed (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (mask : Nat) (hm : mask∈family) (P : ℚ×ℚ)
    (checked : P∈seedPoints (maskSupport mask)) : (owner p mask).Inside P.1 P.2 := by
  have hc := owner_code p hf mask hm
  exact seed_points_sound (p.square (ownerIndex p mask)) (side p mask)
    (by rw [p.congruent]; exact p.side_le) (p.contained _)
    (maskSupport mask) (by simpa only [hc] using coded_exact p (ownerIndex p mask))
    P checked

private theorem apart (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (m n : Nat) (hm : m∈family) (hn : n∈family) (different : m≠n) :
    ∀ x y, ¬ ((owner p m).Inside x y ∧ (owner p n).Inside x y) := by
  apply p.disjoint
  intro same
  exact different ((owner_code p hf m hm).symm.trans
    ((congrArg (markerCode p) same).trans (owner_code p hf n hn)))

theorem family_impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=family) : False := by
  have bottom : (owner p 8448).Inside 2 (457/500) := by
    have h := seed p hf 8448 (by decide +kernel) (2,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have southwest : (owner p 8448).Inside (33/20) (33/20) := by
    have h := seed p hf 8448 (by decide +kernel) (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have singleton : (owner p 1).Inside (87/50) 1 := by
    have h := seed p hf 1 (by decide +kernel) (87/50,1) (by decide +kernel)
    norm_num at h
    exact h
  have southeast : (owner p 512).Inside (47/20) (33/20) := by
    have h := seed p hf 512 (by decide +kernel) (47/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have missingJ : ¬ (owner p 8448).Inside (87/50) 1 := fun h =>
    apart p hf 8448 1 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,singleton⟩
  have missingCentral : ¬ (owner p 8448).Inside (47/20) (33/20) := fun h =>
    apart p hf 8448 512 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,southeast⟩
  have endpoint := C982Merged.reaches_original (owner p 8448) (side p 8448)
    bottom southwest missingJ missingCentral
  have corner : (owner p 12).Inside 3 1 := by
    have h := seed p hf 12 (by decide +kernel) (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owner p 12).Inside (1543/500) 1 := by
    have h := seed p hf 12 (by decide +kernel) (1543/500,1) (by decide +kernel)
    norm_num at h
    exact h
  have wallMarker : (owner p 16384).Inside (1543/500) 2 := by
    have h := seed p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  apply C982Obstruction.impossible_original (owner p 512) (side p 512) southeast
  · intro h
    exact apart p hf 512 12 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,corner⟩
  · intro h
    exact apart p hf 512 12 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,cornerMarker⟩
  · intro h
    exact apart p hf 512 16384 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,wallMarker⟩
  · intro w wn wu h
    have foreign := inside_segment (owner p 8448) 2 (457/500) (23/10) (46/25)
      w bottom endpoint wn wu
    exact apart p hf 512 8448 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ⟨h,foreign⟩

private theorem row_checked :
    (RowIdentity.rowAt 513).originalId=982 ∧ (RowIdentity.rowAt 513).groups=family := by
  decide +kernel

theorem excludes : ExcludesCase 982 := by
  intro r hr he p hf
  exact family_impossible p (hf.trans (RowIdentity.family_at 513 982 family row_checked r hr he))

#print axioms family_impossible
#print axioms excludes
end N12Compact.CommonCases.C982
