import S12.ContinuousPruning
namespace S12
open S12Pilot

structure LeafRelaxation (source target : PoseLeaf) where
  sameReference : source.angle.val.reference 1=target.angle.val.reference 1
  proofs : List FarkasTerms
  checked : ∀ r∈target.inputs,∃ terms∈proofs,LinearImplicationCheck source.inputs r terms

/-- Outward rounding and merging need only certified halfplane implications.
No vertex-enumeration, grid-rounding or convex-hull implementation is trusted. -/
theorem LeafRelaxation.sound {source target : PoseLeaf} (w : LeafRelaxation source target)
    (q : OpenSquare) (h : source.Realizes q) : target.Realizes q := by
  constructor
  · intro r hr
    obtain ⟨terms,_,ht⟩ := w.checked r hr
    exact linear_implication_sound source.inputs r terms ht _ h.1
  · intro P hP
    apply h.2 P
    simpa only [w.sameReference] using hP

/-- Every incoming state is assigned to a checked enclosing output state.
The same output can enclose many inputs, so exact merging is supported. -/
structure DomainRelaxation (sources targets : List PoseLeaf) where
  destination : Fin sources.length → Fin targets.length
  plans : (i : Fin sources.length) → LeafRelaxation (sources.get i) (targets.get (destination i))

theorem DomainRelaxation.sound {sources targets : List PoseLeaf} (w : DomainRelaxation sources targets)
    (q : OpenSquare) (h : PoseCovered sources q) : PoseCovered targets q := by
  obtain ⟨source,hs,hq⟩ := h
  obtain ⟨i,he⟩ := List.mem_iff_get.mp hs
  exact ⟨targets.get (w.destination i),List.get_mem _ _,
    (w.plans i).sound q (by simpa only [he] using hq)⟩

#print axioms DomainRelaxation.sound
end S12
