import S12.AxisOverlapCertificate
import S12.OwnerEnclosure
namespace S12
open S12Pilot
set_option maxHeartbeats 0

structure PruneBlock where
  region : RegionConstraints
  overlaps : List {w : AxisOverlapCertificate // w.Check}

def PruneBlock.Check (w : PruneBlock) (source : PoseLeaf) (neighbors : List PoseLeaf) : Prop :=
  ∀ b∈neighbors,∃ c∈w.overlaps,
    c.val.first.val=source.angle.val.reference 1 ∧ c.val.second.val=b.angle.val.reference 1 ∧
    c.val.inputsA=w.region++source.inputs ∧ c.val.inputsB=b.inputs
instance PruneBlock.decidableCheck (w : PruneBlock) (source : PoseLeaf) (neighbors : List PoseLeaf) :
    Decidable (w.Check source neighbors) := inferInstanceAs (Decidable (∀ b∈neighbors,_))

def PoseCovered (domain : List PoseLeaf) (q : OpenSquare) : Prop := ∃ s∈domain,s.Realizes q

/-- A region can be removed only if every possible state of the other square
forces overlap. The full neighbor cover, including all its boundaries, is used. -/
theorem PruneBlock.sound (w : PruneBlock) (source : PoseLeaf) (neighbors : List PoseLeaf)
    (hw : w.Check source neighbors) (q r : OpenSquare) (hq : source.Realizes q)
    (hr : PoseCovered neighbors r) (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    ¬(∀ f∈w.region,f.Holds ![centerX q,centerY q]) := by
  intro hreg
  obtain ⟨b,hb,hBr⟩ := hr
  obtain ⟨c,_,hca,hcb,hia,hib⟩ := hw b hb
  have hin : ∀ f∈c.val.inputsA,f.Holds ![centerX q,centerY q] := by
    rw [hia]
    intro f hf
    exact (List.mem_append.mp hf).elim (hreg f) (hq.1 f)
  have hh := c.val.sound c.property ![centerX q,centerY q,centerX r,centerY r]
    (by simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using hin)
    (by simpa only [hib,Matrix.cons_val_two,Matrix.cons_val_three] using hBr.1)
  obtain ⟨P,hPq,hPr⟩ := hh
  exact hd P.1 P.2
    ⟨hq.2 P (by simpa only [hca,Matrix.cons_val_zero,Matrix.cons_val_one] using hPq),
      hBr.2 P (by simpa only [hcb,Matrix.cons_val_two,Matrix.cons_val_three] using hPr)⟩

structure PosePruning (source : PoseLeaf) (neighbors : List PoseLeaf) where
  blocks : List {w : PruneBlock // w.Check source neighbors}
  tree : RegionTree
  checked : tree.Check source.inputs (blocks.map (fun b => b.val.region))

def PosePruning.result {source : PoseLeaf} {neighbors : List PoseLeaf}
    (w : PosePruning source neighbors) : List PoseLeaf :=
  (w.tree.leaves source.inputs).map (fun inputs => ⟨source.angle,inputs⟩)

theorem PosePruning.sound {source : PoseLeaf} {neighbors : List PoseLeaf}
    (w : PosePruning source neighbors) (q r : OpenSquare) (hq : source.Realizes q)
    (hr : PoseCovered neighbors r) (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) :
    PoseCovered w.result q := by
  have hf : ∀ block∈w.blocks.map (fun b => b.val.region),
      ¬(∀ f∈block,f.Holds ![centerX q,centerY q]) := by
    intro block hb
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
    exact b.val.sound source neighbors b.property q r hq hr hd
  obtain ⟨inputs,hi,hh⟩ := w.tree.sound source.inputs _ w.checked
    ![centerX q,centerY q] hq.1 hf
  exact ⟨⟨source.angle,inputs⟩,List.mem_map.mpr ⟨inputs,hi,rfl⟩,hh,hq.2⟩

/-- A total indexed list of refinements prevents dropping an unprocessed state. -/
structure DomainPruning (sources neighbors : List PoseLeaf) where
  plans : (i : Fin sources.length) → PosePruning (sources.get i) neighbors

def DomainPruning.result {sources neighbors : List PoseLeaf} (w : DomainPruning sources neighbors) : List PoseLeaf :=
  (List.finRange sources.length).flatMap (fun i => (w.plans i).result)

theorem DomainPruning.sound {sources neighbors : List PoseLeaf} (w : DomainPruning sources neighbors)
    (q r : OpenSquare) (hq : PoseCovered sources q) (hr : PoseCovered neighbors r)
    (hd : ∀ x y,¬(q.Inside x y ∧ r.Inside x y)) : PoseCovered w.result q := by
  obtain ⟨source,hs,hq⟩ := hq
  obtain ⟨i,he⟩ := List.mem_iff_get.mp hs
  have hh := (w.plans i).sound q r (by simpa only [he] using hq) hr hd
  obtain ⟨leaf,hl,hr⟩ := hh
  exact ⟨leaf,List.mem_flatMap.mpr ⟨i,List.mem_finRange i,hl⟩,hr⟩

structure ContinuousPruneStep {n : Nat} (domains : Fin n → List PoseLeaf) where
  target : Fin n
  neighbor : Fin n
  distinct : target≠neighbor
  pruning : DomainPruning (domains target) (domains neighbor)

def ContinuousPruneStep.result {n : Nat} {domains : Fin n → List PoseLeaf}
    (w : ContinuousPruneStep domains) : Fin n → List PoseLeaf :=
  Function.update domains w.target w.pruning.result

/-- One continuous geometric propagation step preserves every actual packing.
Repeated applications therefore justify an entire saved pruning trace. -/
theorem ContinuousPruneStep.sound {n : Nat} {domains : Fin n → List PoseLeaf}
    (w : ContinuousPruneStep domains) (q : Fin n → OpenSquare)
    (hc : ∀ i,PoseCovered (domains i) (q i))
    (hd : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)) :
    ∀ i,PoseCovered (w.result i) (q i) := by
  intro i
  by_cases hi : i=w.target
  · subst i
    simpa only [ContinuousPruneStep.result,Function.update_self] using
      w.pruning.sound (q w.target) (q w.neighbor) (hc w.target) (hc w.neighbor)
        (hd w.target w.neighbor w.distinct)
  · simpa only [ContinuousPruneStep.result,Function.update_of_ne hi] using hc i

#print axioms ContinuousPruneStep.sound
end S12
