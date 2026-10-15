import Compact.Bridge.IndexedCommonPoint
import Compact.Core.EmptyContext

/-! Rectangular common-point and eight-axis groups for arbitrary original
pose dictionaries. A context always retains its actual pose and pruning block.
An absent fan is usable only with an explicit checked affine contradiction.
Range coverage is separate from the numerical/geometric proof of each group.
-/

set_option Elab.async false

namespace N12Compact.IndexedCommonGroups
open S12 S12Pilot IntegerSupport IndexedRelaxation

variable {r m a : Nat} {d : Dictionary r m a}

structure Header (d : Dictionary r m a) where
  pose : Fin m
  block : List (Fin r)

def Header.Realizes (header : Header d) (q : OpenSquare) : Prop :=
  (d.pose header.pose).Realizes q ∧
    ∀ i ∈ header.block, (d.rows i).Holds ![centerX q, centerY q]

/-- Both alternatives carry genuine semantic evidence. A missing fan never
constructs the second alternative automatically. -/
inductive Context (d : Dictionary r m a) where
  | fan (value : IndexedRawPairPlans.PoseContext d)
  | empty (header : Header d) (witness : EmptyContext.Witness r)
      (inputs_exact : witness.inputs = header.block ++ d.poseRows header.pose)
      (checked : witness.Check d.rows)

def Context.header : Context d → Header d
  | .fan value => ⟨value.pose, value.block⟩
  | .empty header _ _ _ => header

def Context.PointCheck (context : Context d) (keys : Nat → Fin 4 → Nat)
    (point : CommonPoint.Point) : Prop :=
  match context with
  | .fan value => CommonPoint.check value.numeric (keys value.keyAngle) point = true
  | .empty _ _ _ _ => True

instance (context : Context d) (keys : Nat → Fin 4 → Nat) (point : CommonPoint.Point) :
    Decidable (context.PointCheck keys point) := by
  cases context <;> unfold Context.PointCheck <;> infer_instance

theorem empty_unrealizable (header : Header d) (witness : EmptyContext.Witness r)
    (inputs_exact : witness.inputs = header.block ++ d.poseRows header.pose)
    (checked : witness.Check d.rows) (positive : ∀ i, 0 < d.denominators i)
    (q : OpenSquare) (realizes : header.Realizes q) : False := by
  have inputs := PairPruning.inputs_hold d.rows d.denominators positive
    (d.poseRows header.pose) _ realizes.1.1
  apply witness.sound d.rows checked ![centerX q, centerY q]
  rw [inputs_exact]
  intro i member
  exact (List.mem_append.mp member).elim (realizes.2 i) (inputs i)

theorem Context.point_sound (context : Context d) (positive : ∀ i, 0 < d.denominators i)
    (keys : Nat → Fin 4 → Nat) (point : CommonPoint.Point)
    (checked : context.PointCheck keys point) (q : OpenSquare)
    (realizes : context.header.Realizes q) : q.Inside point.value.1 point.value.2 := by
  cases context with
  | fan value =>
      exact IndexedCommonPoint.point_sound value positive (keys value.keyAngle) point
        checked q realizes.1 realizes.2
  | empty header witness inputs_exact empty_checked =>
      exact (empty_unrealizable header witness inputs_exact empty_checked positive q realizes).elim

def Context.PairCheck (source neighbor : Context d)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat) : Prop :=
  match source, neighbor with
  | .fan x, .fan y => x.PairCheck y keys opposite
  | _, _ => True

instance (source neighbor : Context d) (keys : Nat → Nat → Fin 8 → Nat)
    (opposite : Nat → Nat) : Decidable (source.PairCheck neighbor keys opposite) := by
  cases source <;> cases neighbor <;> unfold Context.PairCheck <;> infer_instance

def PairOverlaps (source neighbor : Context d) : Prop :=
  ∀ (q t : OpenSquare), source.header.Realizes q → neighbor.header.Realizes t →
    ∃ x y, q.Inside x y ∧ t.Inside x y

theorem Context.pair_sound (source neighbor : Context d)
    (positive : ∀ i, 0 < d.denominators i)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : source.PairCheck neighbor keys opposite) : PairOverlaps source neighbor := by
  intro q t hq ht
  cases source with
  | empty header witness inputs_exact empty_checked =>
      exact (empty_unrealizable header witness inputs_exact empty_checked positive q hq).elim
  | fan x =>
      cases neighbor with
      | empty header witness inputs_exact empty_checked =>
          exact (empty_unrealizable header witness inputs_exact empty_checked positive t ht).elim
      | fan y =>
          exact x.pair_sound y positive keys opposite checked q t hq.1 ht.1 hq.2 ht.2

structure Scope where
  sourceStart : Nat
  sourceCount : Nat
  neighborStart : Nat
  neighborCount : Nat
  deriving DecidableEq

def Scope.Valid (scope : Scope) (u v : Nat) : Prop :=
  scope.sourceStart + scope.sourceCount ≤ u ∧
    scope.neighborStart + scope.neighborCount ≤ v

instance (scope : Scope) (u v : Nat) : Decidable (scope.Valid u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Scope.Covers (scope : Scope) (i j : Nat) : Prop :=
  scope.sourceStart ≤ i ∧ i < scope.sourceStart + scope.sourceCount ∧
    scope.neighborStart ≤ j ∧ j < scope.neighborStart + scope.neighborCount

instance (scope : Scope) (i j : Nat) : Decidable (scope.Covers i j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Scope.sourceIndex {u v : Nat} (scope : Scope) (valid : scope.Valid u v)
    (i : Fin scope.sourceCount) : Fin u := ⟨scope.sourceStart + i.val, by
  have := valid.1
  have := i.isLt
  omega⟩

def Scope.neighborIndex {u v : Nat} (scope : Scope) (valid : scope.Valid u v)
    (j : Fin scope.neighborCount) : Fin v := ⟨scope.neighborStart + j.val, by
  have := valid.2
  have := j.isLt
  omega⟩

theorem Scope.indices_of_covers {u v : Nat} (scope : Scope) (valid : scope.Valid u v)
    (i : Fin u) (j : Fin v) (covered : scope.Covers i.val j.val) :
    ∃ x y, scope.sourceIndex valid x = i ∧ scope.neighborIndex valid y = j := by
  obtain ⟨hs,hsc,hn,hnc⟩ := covered
  refine ⟨⟨i.val - scope.sourceStart, by omega⟩,
    ⟨j.val - scope.neighborStart, by omega⟩, ?_, ?_⟩
  · apply Fin.ext
    dsimp only [Scope.sourceIndex]
    omega
  · apply Fin.ext
    dsimp only [Scope.neighborIndex]
    omega

structure CheckedGroup {u v : Nat}
    (sources : Fin u → Context d) (neighbors : Fin v → Context d) where
  scope : Scope
  sound : ∀ i j, scope.Covers i.val j.val → PairOverlaps (sources i) (neighbors j)

variable {u v : Nat} (sources : Fin u → Context d) (neighbors : Fin v → Context d)

def pointGroup (positive : ∀ i, 0 < d.denominators i)
    (scope : Scope) (valid : scope.Valid u v) (keys : Nat → Fin 4 → Nat)
    (point : CommonPoint.Point)
    (source_checked : ∀ x, (sources (scope.sourceIndex valid x)).PointCheck keys point)
    (neighbor_checked : ∀ y, (neighbors (scope.neighborIndex valid y)).PointCheck keys point) :
    CheckedGroup sources neighbors where
  scope := scope
  sound := by
    intro i j covered q t hq ht
    obtain ⟨x,y,hx,hy⟩ := scope.indices_of_covers valid i j covered
    have xchecked : (sources i).PointCheck keys point := by
      simpa only [hx] using source_checked x
    have ychecked : (neighbors j).PointCheck keys point := by
      simpa only [hy] using neighbor_checked y
    exact ⟨point.value.1, point.value.2,
      (sources i).point_sound positive keys point xchecked q hq,
      (neighbors j).point_sound positive keys point ychecked t ht⟩

def fallbackGroup (positive : ∀ i, 0 < d.denominators i)
    (scope : Scope) (valid : scope.Valid u v)
    (keys : Nat → Nat → Fin 8 → Nat) (opposite : Nat → Nat)
    (checked : ∀ x y, (sources (scope.sourceIndex valid x)).PairCheck
      (neighbors (scope.neighborIndex valid y)) keys opposite) : CheckedGroup sources neighbors where
  scope := scope
  sound := by
    intro i j covered
    obtain ⟨x,y,hx,hy⟩ := scope.indices_of_covers valid i j covered
    apply (sources i).pair_sound (neighbors j) positive keys opposite
    simpa only [hx,hy] using checked x y

def ScopeCheck (scopes : List Scope) (i j : Nat) : Prop :=
  ∃ scope ∈ scopes, scope.Covers i j

instance (scopes : List Scope) (i j : Nat) : Decidable (ScopeCheck scopes i j) := by
  unfold ScopeCheck
  exact List.decidableBEx (fun scope => scope.Covers i j) scopes

theorem groups_sound (groups : List (CheckedGroup sources neighbors)) (scopes : List Scope)
    (exact_scopes : groups.map CheckedGroup.scope = scopes)
    (checked : ∀ (i : Fin u) (j : Fin v), ScopeCheck scopes i.val j.val)
    (i : Fin u) (j : Fin v) : PairOverlaps (sources i) (neighbors j) := by
  obtain ⟨scope,member,covers⟩ := checked i j
  rw [← exact_scopes] at member
  obtain ⟨group,_,equal⟩ := List.mem_map.mp member
  exact group.sound i j (by simpa only [equal] using covers)

/-- Completeness of the actual neighbor list connects group coverage to the
original pruning obligation. A missing or blocked neighbor cannot be omitted. -/
theorem overlap_covered (source : Context d) (domain : List (Fin m))
    (complete : ∀ pose ∈ domain, ∃ j, (neighbors j).header.pose = pose)
    (unblocked : ∀ j, (neighbors j).header.block = [])
    (overlaps : ∀ j, PairOverlaps source (neighbors j))
    (q t : OpenSquare) (hq : source.header.Realizes q)
    (ht : OrientedPoseCovered (domain.map d.pose) t) :
    ∃ x y, q.Inside x y ∧ t.Inside x y := by
  obtain ⟨neighbor,member,realizes⟩ := ht
  obtain ⟨pose,in_domain,rfl⟩ := List.mem_map.mp member
  obtain ⟨j,hj⟩ := complete pose in_domain
  apply overlaps j q t hq
  refine ⟨?_, ?_⟩
  · simpa only [hj] using realizes.1
  · intro i hi
    rw [unblocked j] at hi
    exact False.elim (List.not_mem_nil hi)

#print axioms Context.point_sound
#print axioms Context.pair_sound
#print axioms groups_sound
#print axioms overlap_covered
end N12Compact.IndexedCommonGroups
