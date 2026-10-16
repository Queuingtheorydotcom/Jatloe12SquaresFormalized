import Compact.Bridge.C84Ownership
import Compact.Geometry.C84MergedPair

/-! Whole original case84. Every continuous premise is supplied by an
actual square or by the complete original-budget owner-domain cover.
The two paired corner owners are not removed from the packing; their
unused finite domains are simply unnecessary for this contradiction. -/
namespace N12Compact.C84Complete
open S12 S12Pilot C84Ownership
set_option Elab.async false

theorem family_impossible (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) : False := by
  have exactMarkers (mask : Nat) (member : mask∈family) :
      ExactMarkers (owner p mask) (maskSupport mask) := by
    simpa only [owner,owner_code p hf mask member] using
      coded_exact p (ownerIndex p mask)
  have bottom : (owner p 8704).Inside 2 (457/500) := by
    have h := ((exactMarkers 8704 (by decide +kernel)) 13).mpr (by decide +kernel)
    norm_num [Owns,marker] at h
    exact h
  have southeast : (owner p 8704).Inside (47/20) (33/20) := by
    have h := ((exactMarkers 8704 (by decide +kernel)) 9).mpr (by decide +kernel)
    norm_num [Owns,marker] at h
    exact h
  have southwest : (owner p 2304).Inside (33/20) (33/20) := by
    have h := ((exactMarkers 2304 (by decide +kernel)) 8).mpr (by decide +kernel)
    norm_num [Owns,marker] at h
    exact h
  have northwest : (owner p 2304).Inside (33/20) (47/20) := by
    have h := ((exactMarkers 2304 (by decide +kernel)) 11).mpr (by decide +kernel)
    norm_num [Owns,marker] at h
    exact h
  have right : (owner p 8704).Inside (113/50) 2 := by
    have h := point p hf 8704 16 (by decide +kernel) (by decide)
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have inner : (owner p 2304).Inside (87/50) 2 := by
    have h := point p hf 2304 13 (by decide +kernel) (by decide)
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have cornerG : (owner p 4).Inside (113/50) 1 := by
    have h := point p hf 4 15 (by decide +kernel) (by decide)
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have cornerF : (owner p 4).Inside (12/5) 1 := by
    have h := point p hf 4 6 (by decide +kernel) (by decide)
    norm_num [auxPoints,fPoints,gPoints] at h
    exact h
  have disjoint := apart p hf 8704 2304
    (by decide +kernel) (by decide +kernel) (by decide)
  have cornerApart := apart p hf 8704 4
    (by decide +kernel) (by decide +kernel) (by decide)
  apply C84MergedPair.impossible (owner p 8704) (owner p 2304)
  · change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  · exact (p.congruent _).trans (p.congruent _).symm
  · exact bottom
  · exact southeast
  · exact right
  · exact southwest
  · exact northwest
  · exact inner
  · intro h
    exact disjoint _ _ ⟨h,southwest⟩
  · intro h
    exact cornerApart _ _ ⟨h,cornerG⟩
  · intro h
    exact cornerApart _ _ ⟨h,cornerF⟩
  · exact disjoint

#print axioms family_impossible
end N12Compact.C84Complete
