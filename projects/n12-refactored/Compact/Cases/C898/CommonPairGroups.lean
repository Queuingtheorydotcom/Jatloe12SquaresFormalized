import Compact.Cases.C898.CachedCommonPoint
import Compact.Cases.C898.CachedGeometricPlans
import Compact.Core.RawSupportFanBridge

/-! Shared semantic assembly for rectangular common-point and fallback groups.
The scope checker contains only natural-number ranges. Point/axis arithmetic
is checked separately in bounded opaque facts. No pairwise proof records are
stored, and every original source-neighbor pair must belong to a checked group.
-/

set_option Elab.async false

namespace N12Compact.C898Cached.CommonGroups
open S12 S12Pilot IntegerSupport C898Shared

structure Scope where
  sourceStart : Nat
  sourceCount : Nat
  neighborStart : Nat
  neighborCount : Nat
  deriving DecidableEq

def Scope.Valid (scope : Scope) (m n : Nat) : Prop :=
  scope.sourceStart + scope.sourceCount ≤ m ∧
    scope.neighborStart + scope.neighborCount ≤ n

instance (scope : Scope) (m n : Nat) : Decidable (scope.Valid m n) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Scope.Covers (scope : Scope) (i j : Nat) : Prop :=
  scope.sourceStart ≤ i ∧ i < scope.sourceStart + scope.sourceCount ∧
    scope.neighborStart ≤ j ∧ j < scope.neighborStart + scope.neighborCount

instance (scope : Scope) (i j : Nat) : Decidable (scope.Covers i j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Scope.sourceIndex {m n : Nat} (scope : Scope) (valid : scope.Valid m n)
    (i : Fin scope.sourceCount) : Fin m := ⟨scope.sourceStart + i.val, by
  have := valid.1
  have := i.isLt
  omega⟩

def Scope.neighborIndex {m n : Nat} (scope : Scope) (valid : scope.Valid m n)
    (j : Fin scope.neighborCount) : Fin n := ⟨scope.neighborStart + j.val, by
  have := valid.2
  have := j.isLt
  omega⟩

theorem Scope.indices_of_covers {m n : Nat} (scope : Scope) (valid : scope.Valid m n)
    (i : Fin m) (j : Fin n) (covered : scope.Covers i.val j.val) :
    ∃ a b, scope.sourceIndex valid a = i ∧ scope.neighborIndex valid b = j := by
  obtain ⟨hs, hsc, hn, hnc⟩ := covered
  refine ⟨⟨i.val - scope.sourceStart, by omega⟩,
    ⟨j.val - scope.neighborStart, by omega⟩, ?_, ?_⟩
  · apply Fin.ext
    dsimp only [Scope.sourceIndex]
    omega
  · apply Fin.ext
    dsimp only [Scope.neighborIndex]
    omega

def PairOverlaps (source neighbor : PoseContext) : Prop :=
  ∀ (q t : OpenSquare), (poses source.pose).Realizes q →
    (poses neighbor.pose).Realizes t →
    (∀ k ∈ source.block, (rows k).Holds ![centerX q, centerY q]) →
    ∃ x y, q.Inside x y ∧ t.Inside x y

structure CheckedGroup {m n : Nat}
    (sources : Fin m → PoseContext) (neighbors : Fin n → PoseContext) where
  scope : Scope
  sound : ∀ i j, scope.Covers i.val j.val → PairOverlaps (sources i) (neighbors j)

variable {m n : Nat} (sources : Fin m → PoseContext) (neighbors : Fin n → PoseContext)
  (rawSources : Fin m → RawSupportFan.Context) (rawNeighbors : Fin n → RawSupportFan.Context)
  (sources_exact : ∀ i, rawSources i = (sources i).context.numeric)
  (neighbors_exact : ∀ j, rawNeighbors j = (neighbors j).context.numeric)
  (neighbor_unblocked : ∀ j, (neighbors j).block = [])

def ownKeys (angle : Fin 64) (i : Fin 4) : Nat :=
  fanDirectionKey angle angle ⟨i.val, by omega⟩

/-- One fixed point proves an entire Cartesian rectangle of actual overlaps. -/
noncomputable def pointGroup (scope : Scope) (valid : scope.Valid m n)
    (sourceKeys : Fin m → Fin 4 → Nat) (neighborKeys : Fin n → Fin 4 → Nat)
    (point : CommonPoint.Point)
    (source_checked : ∀ a, CommonPoint.check (rawSources (scope.sourceIndex valid a))
      (sourceKeys (scope.sourceIndex valid a)) point = true)
    (neighbor_checked : ∀ b, CommonPoint.check (rawNeighbors (scope.neighborIndex valid b))
      (neighborKeys (scope.neighborIndex valid b)) point = true) :
    CheckedGroup sources neighbors where
  scope := scope
  sound := by
    intro i j covered q t hq ht block
    obtain ⟨a, b, ha, hb⟩ := scope.indices_of_covers valid i j covered
    have source_check : CommonPoint.check (rawSources i) (sourceKeys i) point = true := by
      simpa only [ha] using source_checked a
    have neighbor_check : CommonPoint.check (rawNeighbors j) (neighborKeys j) point = true := by
      simpa only [hb] using neighbor_checked b
    have source_inside := (sources i).point_sound (rawSources i) (sources_exact i)
      (sourceKeys i) point source_check q hq block
    have neighbor_inside := (neighbors j).point_sound (rawNeighbors j) (neighbors_exact j)
      (neighborKeys j) point neighbor_check t ht
      (by simp only [neighbor_unblocked j, List.not_mem_nil, false_implies, forall_const])
    exact ⟨point.value.1, point.value.2, source_inside, neighbor_inside⟩

/-- An unsuccessful point search retains the original eight-axis obligation. -/
noncomputable def fallbackGroup (scope : Scope) (valid : scope.Valid m n)
    (sourceAngles : Fin m → Fin 64) (neighborAngles : Fin n → Fin 64)
    (source_angles_exact : ∀ i, sourceAngles i = (sources i).keyAngle)
    (neighbor_angles_exact : ∀ j, neighborAngles j = (neighbors j).keyAngle)
    (checked : ∀ a b,
      let i := scope.sourceIndex valid a
      let j := scope.neighborIndex valid b
      RawSupportFan.PairCheck (rawSources i) (rawNeighbors j)
        (fanDirectionKey (sourceAngles i) (neighborAngles j))
        (fun key => (key + 128) % 256)) : CheckedGroup sources neighbors where
  scope := scope
  sound := by
    intro i j covered q t hq ht block
    obtain ⟨a, b, ha, hb⟩ := scope.indices_of_covers valid i j covered
    have raw_checked : RawSupportFan.PairCheck (rawSources i) (rawNeighbors j)
        (fanDirectionKey (sourceAngles i) (neighborAngles j))
        (fun key => (key + 128) % 256) := by
      simpa only [ha, hb] using checked a b
    have original : (sources i).PairCheck (neighbors j) := by
      apply CachedSupportFan.PairCheck.of_cached_numeric
        (sources i).context (neighbors j).context (rawSources i) (rawNeighbors j)
        (sources_exact i) (neighbors_exact j)
        (fanDirectionKey (sources i).keyAngle (neighbors j).keyAngle)
        (fun key => (key + 128) % 256)
      simpa only [source_angles_exact i, neighbor_angles_exact j] using raw_checked
    exact (sources i).pair_sound (neighbors j) original q t hq ht block
      (by simp only [neighbor_unblocked j, List.not_mem_nil, false_implies, forall_const])

def ScopeCheck (scopes : List Scope) (i j : Nat) : Prop :=
  ∃ scope ∈ scopes, scope.Covers i j

instance (scopes : List Scope) (i j : Nat) : Decidable (ScopeCheck scopes i j) := by
  unfold ScopeCheck
  exact List.decidableBEx (fun scope => scope.Covers i j) scopes

theorem groups_sound (groups : List (CheckedGroup sources neighbors)) (scopes : List Scope)
    (exact_scopes : groups.map CheckedGroup.scope = scopes)
    (checked : ∀ (i : Fin m) (j : Fin n), ScopeCheck scopes i.val j.val)
    (i : Fin m) (j : Fin n) : PairOverlaps (sources i) (neighbors j) := by
  obtain ⟨scope, member, covers⟩ := checked i j
  rw [← exact_scopes] at member
  obtain ⟨group, _, equal⟩ := List.mem_map.mp member
  exact group.sound i j (by simpa only [equal] using covers)

#print axioms pointGroup
#print axioms fallbackGroup
#print axioms groups_sound

end N12Compact.C898Cached.CommonGroups
