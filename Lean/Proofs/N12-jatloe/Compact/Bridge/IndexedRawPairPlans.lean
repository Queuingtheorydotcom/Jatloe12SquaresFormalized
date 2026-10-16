import Compact.Bridge.IndexedCachedPairPlans
import Compact.Core.RawSupportFan

/-! Indexed pruning with a proof-free numerical cache.
Each raw cache is linked by ordinary equality to a certified fan. Numerical
pair replay uses only the two raw contexts and exact eight-axis arithmetic;
all original rows, orientations, neighbor poses and strict complements remain
in the semantic step theorem inherited from the indexed plan interface. -/

set_option Elab.async false

namespace N12Compact.IndexedRawPairPlans
open S12 S12Pilot IntegerSupport PairPruning IndexedRelaxation IndexedCachedPairPlans

variable {r m a : Nat}

structure PoseContext (d : Dictionary r m a) extends IndexedCachedPairPlans.PoseContext d where
  numeric : RawSupportFan.Context
  numeric_exact : numeric = context.numeric

variable {d : Dictionary r m a}

def PoseContext.PairCheck (x y : PoseContext d)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat) : Prop :=
  RawSupportFan.PairCheck x.numeric y.numeric (keys x.keyAngle y.keyAngle) opposite

instance (x y : PoseContext d) (keys : Nat → Nat → Fin 8 → Nat)
    (opposite : Nat → Nat) : Decidable (x.PairCheck y keys opposite) :=
  inferInstanceAs (Decidable (RawSupportFan.PairCheck _ _ _ _))

theorem PoseContext.pair_sound (x y : PoseContext d)
    (positive : ∀ i, 0 < d.denominators i)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : x.PairCheck y keys opposite)
    (q t : OpenSquare) (hq : (d.pose x.pose).Realizes q)
    (ht : (d.pose y.pose).Realizes t)
    (hxBlock : ∀ i ∈ x.block, (d.rows i).Holds ![centerX q, centerY q])
    (hyBlock : ∀ i ∈ y.block, (d.rows i).Holds ![centerX t, centerY t]) :
    ∃ u v, q.Inside u v ∧ t.Inside u v := by
  have xr : x.numeric.reference = x.context.reference := by rw [x.numeric_exact]; rfl
  have yr : y.numeric.reference = y.context.reference := by rw [y.numeric_exact]; rfl
  have hxc : x.numeric.reference.value.Check := by
    rw [xr, x.reference_exact]
    exact (d.pose x.pose).angle.val.reference_checked
      (d.pose x.pose).angle.property 1 (by norm_num)
  have hyc : y.numeric.reference.value.Check := by
    rw [yr, y.reference_exact]
    exact (d.pose y.pose).angle.val.reference_checked
      (d.pose y.pose).angle.property 1 (by norm_num)
  have hx : ∀ i ∈ d.poseRows x.pose, (d.rows i).Holds ![centerX q, centerY q] :=
    inputs_hold d.rows d.denominators positive (d.poseRows x.pose) _ hq.1
  have hy : ∀ i ∈ d.poseRows y.pose, (d.rows i).Holds ![centerX t, centerY t] :=
    inputs_hold d.rows d.denominators positive (d.poseRows y.pose) _ ht.1
  have overlap := RawSupportFan.pair_sound x.numeric y.numeric
    (fun p => ∀ i ∈ x.context.inputs, (d.rows i).Holds p)
    (fun p => ∀ i ∈ y.context.inputs, (d.rows i).Holds p)
    (x.context.cached_numeric_valid x.numeric x.numeric_exact)
    (y.context.cached_numeric_valid y.numeric y.numeric_exact)
    (by rw [xr]; exact x.reference_valid) (by rw [yr]; exact y.reference_valid)
    hxc hyc (keys x.keyAngle y.keyAngle) opposite checked
    ![centerX q, centerY q] ![centerX t, centerY t]
    (by rw [x.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (hxBlock i) (hx i))
    (by rw [y.inputs_exact]; intro i hi
        exact (List.mem_append.mp hi).elim (hyBlock i) (hy i))
  obtain ⟨P, hPq, hPt⟩ := overlap
  refine ⟨P.1, P.2, hq.2 P ?_, ht.2 P ?_⟩
  · simpa only [xr, x.reference_exact, Matrix.cons_val_zero, Matrix.cons_val_one] using hPq
  · simpa only [yr, y.reference_exact, Matrix.cons_val_zero, Matrix.cons_val_one] using hPt

theorem PoseContext.block_forbidden {n : Nat} (source : PoseContext d)
    (positive : ∀ i, 0 < d.denominators i)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (neighbors : Fin n → PoseContext d) (domain : List (Fin m))
    (complete : ∀ pose ∈ domain, ∃ j, (neighbors j).pose = pose)
    (unblocked : ∀ j, (neighbors j).block = [])
    (checked : ∀ j, source.PairCheck (neighbors j) keys opposite)
    (q t : OpenSquare) (hq : (d.pose source.pose).Realizes q)
    (ht : OrientedPoseCovered (domain.map d.pose) t)
    (disjoint : ∀ u v, ¬(q.Inside u v ∧ t.Inside u v)) :
    ¬(∀ i ∈ source.block, (d.rows i).Holds ![centerX q, centerY q]) := by
  intro holds
  obtain ⟨neighbor, member, realizes⟩ := ht
  obtain ⟨neighbor, in_domain, rfl⟩ := List.mem_map.mp member
  obtain ⟨j, hj⟩ := complete neighbor in_domain
  obtain ⟨u, v, overlap⟩ := source.pair_sound (neighbors j) positive keys opposite
    (checked j) q t hq (by simpa only [hj] using realizes.1) holds
    (by intro i hi; simp [unblocked j] at hi)
  exact disjoint u v overlap

/-- One semantic transition consumes the complete original source/neighbor
covers and checked outside-block pieces. It introduces no geometric premise. -/
theorem step_sound {u v : Nat} (d : Dictionary r m a)
    (positive : ∀ i, 0 < d.denominators i)
    (blockRows : Nat → List (Fin r)) (complement : Fin r → Fin r)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (sources neighbors pieces : List (Fin m)) (plans : List (Plan m))
    (sourceContexts : Fin u → PoseContext d) (neighborContexts : Fin v → PoseContext d)
    (covered : StepCover sources pieces plans)
    (plans_checked : ∀ plan ∈ plans, plan.Check d blockRows complement)
    (source_matches : ∀ plan ∈ plans, ∀ block, plan.block = some block →
      ∃ i, (sourceContexts i).pose = plan.source ∧ (sourceContexts i).block = blockRows block)
    (neighbor_complete : ∀ pose ∈ neighbors, ∃ j, (neighborContexts j).pose = pose)
    (neighbor_unblocked : ∀ j, (neighborContexts j).block = [])
    (pairs_checked : ∀ i j, (sourceContexts i).PairCheck (neighborContexts j) keys opposite)
    (q t : OpenSquare) (hq : OrientedPoseCovered (sources.map d.pose) q)
    (ht : OrientedPoseCovered (neighbors.map d.pose) t)
    (disjoint : ∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) :
    OrientedPoseCovered (pieces.map d.pose) q := by
  obtain ⟨source, member, realizes⟩ := hq
  obtain ⟨source, in_sources, rfl⟩ := List.mem_map.mp member
  obtain ⟨plan, hp, he, hpieces⟩ := covered source in_sources
  have plan_realizes : (d.pose plan.source).OrientedRealizes q := by
    simpa only [he] using realizes
  have forbidden : ∀ block, plan.block = some block →
      ¬(∀ i ∈ blockRows block, (d.rows i).Holds ![centerX q, centerY q]) := by
    intro block hb
    obtain ⟨i, hi, hblock⟩ := source_matches plan hp block hb
    have hf := (sourceContexts i).block_forbidden positive keys opposite
      neighborContexts neighbors neighbor_complete neighbor_unblocked (pairs_checked i) q t
      (by simpa only [hi] using plan_realizes.1) ht disjoint
    simpa only [hblock] using hf
  obtain ⟨piece, member, realizes⟩ := plan.sound d blockRows complement positive
    (plans_checked plan hp) q plan_realizes forbidden
  obtain ⟨piece, in_pieces, rfl⟩ := List.mem_map.mp member
  exact ⟨d.pose piece, List.mem_map.mpr ⟨piece, hpieces piece in_pieces, rfl⟩, realizes⟩

#print axioms PoseContext.pair_sound
#print axioms step_sound
end N12Compact.IndexedRawPairPlans
