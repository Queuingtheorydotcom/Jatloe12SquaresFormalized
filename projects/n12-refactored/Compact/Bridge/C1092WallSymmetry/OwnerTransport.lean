import Compact.Bridge.C1092WallSymmetry.OwnerFacts

/-! Exact family and physical-square transport under the genuine container symmetries. -/
namespace N12Compact.C1092WallSymmetry
open S12 S12Pilot C1092WallCycle
set_option Elab.async false

private theorem exact_owner_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    ExactMarkers (g.pull (owners p (ownerAction g i))) (maskSupport (ownerCode i)) := by
  intro j
  rw [owns_transform,owners_markers p hf (ownerAction g i) (g.markerAction j)]
  exact FiniteFacts.owner_marker_transport g.swap g.reflectX g.reflectY i j

private theorem pull_owner_code (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    markerCode (g.pullPacking p) (ownerIndex p (ownerCode (ownerAction g i))) =
      ownerCode i := by
  have hp := exact_owner_transport g p hf i
  have code := coded_exact (g.pullPacking p)
    (ownerIndex p (ownerCode (ownerAction g i)))
  have same : maskSupport (markerCode (g.pullPacking p)
      (ownerIndex p (ownerCode (ownerAction g i)))) = maskSupport (ownerCode i) := by
    apply Finset.ext
    intro j
    exact (code j).symm.trans (hp j)
  have candidate := FiniteFacts.owner_code_candidate
  exact candidate_support_injective _ _ (markerCode_spec _ _).1 (candidate i) same

/-- Every container symmetry preserves this entire original marker family. -/
theorem family_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) : codedMarkerFamily (g.pullPacking p) = family := by
  have subset : family ⊆ codedMarkerFamily (g.pullPacking p) := by
    intro m hm
    have enumerated := FiniteFacts.family_enumerated
    obtain ⟨i,rfl⟩ := enumerated m hm
    exact Finset.mem_image.mpr
      ⟨ownerIndex p (ownerCode (ownerAction g i)),Finset.mem_univ _,pull_owner_code g p hf i⟩
  apply (Finset.eq_of_subset_of_card_le subset _).symm
  rw [codedMarkerFamily_card]
  decide

/-- This is equality of physical squares, not just an equality of masks.
The original packing index is identified using marker-code injectivity. -/
theorem owners_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (i : Fin 12) :
    owners (g.pullPacking p) i = g.pull (owners p (ownerAction g i)) := by
  have index : ownerIndex (g.pullPacking p) (ownerCode i) =
      ownerIndex p (ownerCode (ownerAction g i)) := by
    apply markerCode_injective (g.pullPacking p)
    exact (owner_code _ (family_transport g p hf) i).trans (pull_owner_code g p hf i).symm
  unfold owners
  rw [index]
  rfl

theorem central_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (k : Fin 4) :
    owners (g.pullPacking p) (centralOwner k) =
      g.pull (owners p (centralOwner (centralAction g k))) := by
  rw [owners_transport g p hf,ownerAction_central]

theorem wall_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (k : Fin 4) :
    owners (g.pullPacking p) (wallOwner k) =
      g.pull (owners p (wallOwner (wallAction g k))) := by
  rw [owners_transport g p hf,ownerAction_wall]

theorem corner_transport (g : Transform) (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) (k : Fin 4) :
    owners (g.pullPacking p) (cornerOwner k) =
      g.pull (owners p (cornerOwner (centralAction g k))) := by
  rw [owners_transport g p hf,ownerAction_corner]

end N12Compact.C1092WallSymmetry
