import S12.DomainRelaxation
namespace S12
open S12Pilot
set_option maxHeartbeats 0

deriving instance DecidableEq for PoseLeaf

/-- Data form of a halfplane relaxation; its arithmetic check has a proved
meaning independent of the program that proposed the polygon. -/
structure RelaxationLink where
  source : PoseLeaf
  target : PoseLeaf
  proofs : List FarkasTerms

def RelaxationLink.Check (w : RelaxationLink) : Prop :=
  w.source.angle.val.reference 1=w.target.angle.val.reference 1 ∧
  ∀ r∈w.target.inputs,∃ terms∈w.proofs,LinearImplicationCheck w.source.inputs r terms
instance RelaxationLink.decidableCheck (w : RelaxationLink) : Decidable w.Check :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem RelaxationLink.sound (w : RelaxationLink) (hw : w.Check) (q : OpenSquare)
    (h : w.source.Realizes q) : w.target.Realizes q :=
  (⟨hw.1,w.proofs,hw.2⟩ : LeafRelaxation w.source w.target).sound q h

def RelaxationCoverCheck (sources targets : List PoseLeaf)
    (links : List {w : RelaxationLink // w.Check}) : Prop :=
  ∀ s∈sources,∃ w∈links,w.val.source=s ∧ w.val.target∈targets
instance decidableRelaxationCoverCheck (sources targets : List PoseLeaf) (links : List {w : RelaxationLink // w.Check}) :
    Decidable (RelaxationCoverCheck sources targets links) :=
  inferInstanceAs (Decidable (∀ s∈sources,_))

theorem relaxation_cover_sound (sources targets : List PoseLeaf)
    (links : List {w : RelaxationLink // w.Check})
    (hw : RelaxationCoverCheck sources targets links) (q : OpenSquare)
    (h : PoseCovered sources q) : PoseCovered targets q := by
  obtain ⟨s,hs,hq⟩ := h
  obtain ⟨w,_,he,ht⟩ := hw s hs
  exact ⟨w.val.target,ht,w.val.sound w.property q (by simpa only [he] using hq)⟩

/-- A complete continuous cut for one source state, with an explicitly checked
cover of every retained piece after outward rounding and merging. -/
structure CertifiedPosePruning where
  source : PoseLeaf
  neighbors : List PoseLeaf
  pruning : PosePruning source neighbors
  targets : List PoseLeaf
  links : List {w : RelaxationLink // w.Check}
  covered : RelaxationCoverCheck pruning.result targets links

theorem CertifiedPosePruning.sound (w : CertifiedPosePruning) (q r : OpenSquare)
    (hq : w.source.Realizes q) (hr : PoseCovered w.neighbors r)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : PoseCovered w.targets q :=
  relaxation_cover_sound _ _ w.links w.covered q (w.pruning.sound q r hq hr hd)

def PruningCoverCheck (sources neighbors targets : List PoseLeaf)
    (plans : List CertifiedPosePruning) : Prop :=
  ∀ s∈sources,∃ w∈plans,w.source=s ∧ w.neighbors=neighbors ∧
    ∀ t∈w.targets,t∈targets
instance decidablePruningCoverCheck (sources neighbors targets : List PoseLeaf) (plans : List CertifiedPosePruning) :
    Decidable (PruningCoverCheck sources neighbors targets plans) :=
  inferInstanceAs (Decidable (∀ s∈sources,_))

/-- Coverage, not the search trace, is the trust boundary: every source state
must have a plan and every result must appear in the next enclosure. -/
theorem pruning_cover_sound (sources neighbors targets : List PoseLeaf)
    (plans : List CertifiedPosePruning)
    (hw : PruningCoverCheck sources neighbors targets plans) (q r : OpenSquare)
    (hq : PoseCovered sources q) (hr : PoseCovered neighbors r)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : PoseCovered targets q := by
  obtain ⟨s,hs,hq⟩ := hq
  obtain ⟨w,_,he,hn,ht⟩ := hw s hs
  obtain ⟨t,hm,hq⟩ := w.sound q r (by simpa only [he] using hq) (by simpa only [hn] using hr) hd
  exact ⟨t,ht t hm,hq⟩

#print axioms pruning_cover_sound
end S12
