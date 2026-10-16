import Compact.Bridge.AxisSection
import Compact.Bridge.DirectPruningPlan

/-! A dictionary-independent chord transition. Every incoming pose has two
strict interval-complement branches. Each whole branch implies an original
outgoing pose or a checked contradiction; no historical subdivision is kept.
Local row caches are bound by equalities to the original pose dictionary. -/

set_option Elab.async false

namespace N12Compact.IndexedChord
open S12 S12Pilot IntegerSupport IndexedRelaxation AngleSection

variable {r m a : Nat}
variable {d : Dictionary r m a} {horizontal : Bool} {lo hi : ℚ}

theorem pose_rows_hold (d : Dictionary r m a) (positive : ∀ i, 0 < d.denominators i)
    (source : Fin m) (q : OpenSquare) (incoming : (d.pose source).OrientedRealizes q) :
    ∀ row ∈ (d.poseRows source).map d.rows, row.Holds ![centerX q,centerY q] := by
  intro row member
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp member
  apply ((d.rows i).normalized_holds_iff _ (positive i) _).mp
  exact incoming.1.1 _ (List.mem_map.mpr ⟨i,hi,rfl⟩)

/-- Numeric implication checks reduce a local target cache, while this
single identity binds that cache to every original target constraint. -/
theorem keep_checked (d : Dictionary r m a) (source target : Fin m)
    (inputs targets : List Row) (hints : List RelaxationHints.Hint)
    (targets_exact : targets = (d.poseRows target).map d.rows)
    (same_angle : d.poseAngle source = d.poseAngle target)
    (numeric : RelaxationHints.Check inputs targets hints) :
    (DirectPruningPlan.Branch.mk inputs (.keep target hints)).Check d source := by
  exact ⟨same_angle, by simpa only [targets_exact] using numeric⟩

structure Neighbor (d : Dictionary r m a) where
  source : Fin m
  radius : Radius
  inputs : List Row
  inputs_exact : inputs = (d.poseRows source).map d.rows
  hints : List RelaxationHints.Hint

def Neighbor.bounds (entry : Neighbor d) (horizontal : Bool) (lo hi : ℚ) : List Row :=
  [AxisSection.lower horizontal (hi-entry.radius.radius) false,
   AxisSection.upper horizontal (lo+entry.radius.radius) false]

def Neighbor.Check (entry : Neighbor d) (horizontal : Bool) (lo hi : ℚ) : Prop :=
  entry.radius.Check (d.pose entry.source).angle.val ∧
  RelaxationHints.Check entry.inputs (entry.bounds horizontal lo hi) entry.hints

instance (entry : Neighbor d) (horizontal : Bool) (lo hi : ℚ) :
    Decidable (entry.Check horizontal lo hi) := inferInstanceAs (Decidable (_ ∧ _))

theorem Neighbor.sound (entry : Neighbor d) (horizontal : Bool) (lo hi : ℚ)
    (positive : ∀ i, 0 < d.denominators i) (checked : entry.Check horizontal lo hi)
    (q : OpenSquare) (side : 1 < q.side)
    (incoming : (d.pose entry.source).OrientedRealizes q)
    (cut : ℝ) (low : (lo : ℝ) ≤ cut) (high : cut ≤ (hi : ℝ)) :
    AxisSection.Section horizontal q cut := by
  have inputs := pose_rows_hold d positive entry.source q incoming
  rw [← entry.inputs_exact] at inputs
  have bounds := RelaxationHints.sound checked.2 _ inputs
  have lower := (AxisSection.holds_lower horizontal (hi-entry.radius.radius) false q).mp
    (bounds _ (by simp [Neighbor.bounds]))
  have upper := (AxisSection.holds_upper horizontal (lo+entry.radius.radius) false q).mp
    (bounds _ (by simp [Neighbor.bounds]))
  simp only [Bool.false_eq_true,↓reduceIte] at lower upper
  push_cast at lower upper
  apply AxisSection.oriented_section horizontal (d.pose entry.source) entry.radius
    checked.1 q side incoming.2 cut
  apply abs_le.mpr
  constructor <;> linarith

structure Plan (d : Dictionary r m a) (horizontal : Bool) (lo hi : ℚ) where
  source : Fin m
  radius : Radius
  low : DirectPruningPlan.Branch m
  high : DirectPruningPlan.Branch m
  low_inputs : low.inputs =
    AxisSection.upper horizontal (lo-radius.radius) true :: (d.poseRows source).map d.rows
  high_inputs : high.inputs =
    AxisSection.lower horizontal (hi+radius.radius) true :: (d.poseRows source).map d.rows

def Plan.targets (plan : Plan d horizontal lo hi) : List (Fin m) :=
  plan.low.targets ++ plan.high.targets

def Plan.Check (plan : Plan d horizontal lo hi) : Prop :=
  plan.radius.Check (d.pose plan.source).angle.val ∧
  plan.low.Check d plan.source ∧ plan.high.Check d plan.source

instance (plan : Plan d horizontal lo hi) : Decidable plan.Check :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Plan.sound (plan : Plan d horizontal lo hi) (ordered : lo ≤ hi)
    (positive : ∀ i, 0 < d.denominators i) (checked : plan.Check)
    (q : Fin 4 → OpenSquare) (side : ∀ i, 1 < (q i).side)
    (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : (d.pose plan.source).OrientedRealizes (q 0))
    (neighbors : ∀ cut, (lo : ℝ) ≤ cut → cut ≤ (hi : ℝ) →
      ∀ i : Fin 3, AxisSection.Section horizontal (q i.succ) cut) :
    OrientedPoseCovered (plan.targets.map d.pose) (q 0) := by
  have excluded := AxisSection.window_excludes horizontal lo hi (by exact_mod_cast ordered)
    q (d.pose plan.source) plan.radius checked.1 side box disjoint incoming neighbors
  have outside : AxisSection.center horizontal (q 0) < ((lo-plan.radius.radius : ℚ) : ℝ) ∨
      ((hi+plan.radius.radius : ℚ) : ℝ) < AxisSection.center horizontal (q 0) := by
    push_cast
    by_contra h
    push_neg at h
    exact excluded h
  have inputs := pose_rows_hold d positive plan.source (q 0) incoming
  rcases outside with low | high
  · have bound := (AxisSection.holds_upper horizontal (lo-plan.radius.radius) true (q 0)).mpr low
    obtain ⟨pose,member,realizes⟩ := plan.low.sound d plan.source positive checked.2.1 (q 0) incoming
      (by rw [plan.low_inputs]; intro row member; rcases List.mem_cons.mp member with rfl | member
          · exact bound
          · exact inputs row member)
    exact ⟨pose, by simpa only [Plan.targets,List.map_append] using List.mem_append_left _ member, realizes⟩
  · have bound := (AxisSection.holds_lower horizontal (hi+plan.radius.radius) true (q 0)).mpr high
    obtain ⟨pose,member,realizes⟩ := plan.high.sound d plan.source positive checked.2.2 (q 0) incoming
      (by rw [plan.high_inputs]; intro row member; rcases List.mem_cons.mp member with rfl | member
          · exact bound
          · exact inputs row member)
    exact ⟨pose, by simpa only [Plan.targets,List.map_append] using List.mem_append_right _ member, realizes⟩

theorem neighbor_cover (d : Dictionary r m a) (horizontal : Bool) (lo hi : ℚ)
    (positive : ∀ i, 0 < d.denominators i) (domain : List (Fin m))
    (entries : List (Neighbor d)) (same_sources : entries.map Neighbor.source = domain)
    (checked : ∀ entry ∈ entries, entry.Check horizontal lo hi)
    (q : OpenSquare) (side : 1 < q.side)
    (incoming : OrientedPoseCovered (domain.map d.pose) q)
    (cut : ℝ) (low : (lo : ℝ) ≤ cut) (high : cut ≤ (hi : ℝ)) :
    AxisSection.Section horizontal q cut := by
  obtain ⟨pose,member,realizes⟩ := incoming
  obtain ⟨source,in_domain,rfl⟩ := List.mem_map.mp member
  rw [← same_sources] at in_domain
  obtain ⟨entry,in_entries,same_source⟩ := List.mem_map.mp in_domain
  exact entry.sound horizontal lo hi positive (checked entry in_entries) q side
    (by simpa only [same_source] using realizes) cut low high

theorem plans_cover (d : Dictionary r m a) (horizontal : Bool) (lo hi : ℚ)
    (ordered : lo ≤ hi) (positive : ∀ i, 0 < d.denominators i)
    (sources targets : List (Fin m)) (plans : List (Plan d horizontal lo hi))
    (same_sources : plans.map Plan.source = sources)
    (included : ∀ plan ∈ plans, ∀ target ∈ plan.targets, target ∈ targets)
    (checked : ∀ plan ∈ plans, plan.Check)
    (q : Fin 4 → OpenSquare) (side : ∀ i, 1 < (q i).side)
    (box : ∀ i, InsideContainer (q i))
    (disjoint : ∀ i j, i ≠ j → ∀ x y, ¬ ((q i).Inside x y ∧ (q j).Inside x y))
    (incoming : OrientedPoseCovered (sources.map d.pose) (q 0))
    (neighbors : ∀ cut, (lo : ℝ) ≤ cut → cut ≤ (hi : ℝ) →
      ∀ i : Fin 3, AxisSection.Section horizontal (q i.succ) cut) :
    OrientedPoseCovered (targets.map d.pose) (q 0) := by
  obtain ⟨pose,member,realizes⟩ := incoming
  obtain ⟨source,in_sources,rfl⟩ := List.mem_map.mp member
  rw [← same_sources] at in_sources
  obtain ⟨plan,in_plans,same_source⟩ := List.mem_map.mp in_sources
  obtain ⟨pose,member,realizes⟩ := plan.sound ordered positive (checked plan in_plans)
    q side box disjoint (by simpa only [same_source] using realizes) neighbors
  obtain ⟨target,in_targets,rfl⟩ := List.mem_map.mp member
  exact ⟨d.pose target,List.mem_map.mpr ⟨target,included plan in_plans target in_targets,rfl⟩,realizes⟩

#print axioms Plan.sound
#print axioms plans_cover
end N12Compact.IndexedChord
