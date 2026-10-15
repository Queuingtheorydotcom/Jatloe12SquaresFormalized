import Compact.Core.RowSupport
import S12.OrientedCoverage

/-!
# Shared integer supports preserve original oriented pose coverage

Only row identities, membership, and angle identifiers are checked here.
The decoded poses retain the original `S12.PoseLeaf` semantics. A numerical
support is proved once and may be reused by arbitrarily many relaxation links.
-/

namespace N12Compact.IndexedRelaxation

open IntegerSupport S12

structure Support (n : Nat) where
  target : Fin n
  left : Fin n
  right : Fin n
  deriving DecidableEq

def Support.Check {n : Nat} (w : Support n) (rows : Fin n → Row) : Prop :=
  RowSupport.Check (rows w.left) (rows w.right) (rows w.target)

instance {n : Nat} (w : Support n) (rows : Fin n → Row) : Decidable (w.Check rows) :=
  inferInstanceAs (Decidable (RowSupport.Check _ _ _))

structure Dictionary (n m a : Nat) where
  rows : Fin n → Row
  denominators : Fin n → Nat
  angles : Fin a → {w : AngleEnclosure // w.Check}
  poseAngle : Fin m → Fin a
  poseRows : Fin m → List (Fin n)

def Dictionary.pose {n m a : Nat} (d : Dictionary n m a) (i : Fin m) : PoseLeaf :=
  ⟨d.angles (d.poseAngle i),
    (d.poseRows i).map (fun r => (d.rows r).normalized (d.denominators r))⟩

theorem Dictionary.transfer {n m a : Nat} (d : Dictionary n m a)
    {source target : Fin m} (same_angle : d.poseAngle source = d.poseAngle target)
    (positive : ∀ r, 0 < d.denominators r) (q : S12Pilot.OpenSquare)
    (h : (d.pose source).OrientedRealizes q)
    (ht : ∀ r ∈ d.poseRows target, (d.rows r).Holds ![centerX q, centerY q]) :
    (d.pose target).OrientedRealizes q := by
  have angle_eq : (d.pose source).angle = (d.pose target).angle := by
    change d.angles (d.poseAngle source) = d.angles (d.poseAngle target)
    rw [same_angle]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    exact ((d.rows r).normalized_holds_iff _ (positive r) _).mpr (ht r hr)
  · intro point hp
    apply h.1.2 point
    simpa only [angle_eq] using hp
  · simpa only [PoseLeaf.AngleWitness, angle_eq] using h.2

structure Link (m k : Nat) where
  source : Fin m
  target : Fin m
  supports : List (Fin k)
  deriving DecidableEq

def Link.Check {n m a k : Nat} (w : Link m k) (d : Dictionary n m a)
    (rules : Fin k → Support n) : Prop :=
  d.poseAngle w.source = d.poseAngle w.target ∧
  ∀ r ∈ d.poseRows w.target, r ∈ d.poseRows w.source ∨
    ∃ i ∈ w.supports, (rules i).target = r ∧
      (rules i).left ∈ d.poseRows w.source ∧ (rules i).right ∈ d.poseRows w.source

instance {n m a k : Nat} (w : Link m k) (d : Dictionary n m a)
    (rules : Fin k → Support n) : Decidable (w.Check d rules) := by
  unfold Link.Check
  letI : DecidablePred (fun r => r ∈ d.poseRows w.source ∨
      ∃ i ∈ w.supports, (rules i).target = r ∧
        (rules i).left ∈ d.poseRows w.source ∧ (rules i).right ∈ d.poseRows w.source) :=
    fun r => by
      letI : Decidable (∃ i ∈ w.supports, (rules i).target = r ∧
          (rules i).left ∈ d.poseRows w.source ∧ (rules i).right ∈ d.poseRows w.source) :=
        List.decidableBEx _ w.supports
      infer_instance
  letI : Decidable (∀ r ∈ d.poseRows w.target, r ∈ d.poseRows w.source ∨
      ∃ i ∈ w.supports, (rules i).target = r ∧
        (rules i).left ∈ d.poseRows w.source ∧ (rules i).right ∈ d.poseRows w.source) :=
    List.decidableBAll _ (d.poseRows w.target)
  infer_instance

theorem Link.sound {n m a k : Nat} (w : Link m k) (d : Dictionary n m a)
    (rules : Fin k → Support n) (checked : w.Check d rules)
    (positive : ∀ r, 0 < d.denominators r)
    (rules_checked : ∀ i, (rules i).Check d.rows)
    (q : S12Pilot.OpenSquare) (h : (d.pose w.source).OrientedRealizes q) :
    (d.pose w.target).OrientedRealizes q := by
  have angle_eq : (d.pose w.source).angle = (d.pose w.target).angle := by
    change d.angles (d.poseAngle w.source) = d.angles (d.poseAngle w.target)
    rw [checked.1]
  have source_holds : ∀ r ∈ d.poseRows w.source,
      (d.rows r).Holds ![centerX q, centerY q] := by
    intro r hr
    apply ((d.rows r).normalized_holds_iff _ (positive r) _).mp
    exact h.1.1 _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro row hrow
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
    apply ((d.rows r).normalized_holds_iff _ (positive r) _).mpr
    rcases checked.2 r hr with hs | ⟨i, _, he, hl, hright⟩
    · exact source_holds r hs
    · rw [← he]
      exact RowSupport.sound (rules_checked i) _
        (source_holds _ hl) (source_holds _ hright)
  · intro point hp
    apply h.1.2 point
    simpa only [angle_eq] using hp
  · simpa only [PoseLeaf.AngleWitness, angle_eq] using h.2

def CoverCheck {m k : Nat} (sources targets : List (Fin m))
    (links : List (Link m k)) : Prop :=
  ∀ s ∈ sources, ∃ w ∈ links, w.source = s ∧ w.target ∈ targets

instance {m k : Nat} (sources targets : List (Fin m)) (links : List (Link m k)) :
    Decidable (CoverCheck sources targets links) := by
  unfold CoverCheck
  letI : DecidablePred (fun s => ∃ w ∈ links, w.source = s ∧ w.target ∈ targets) :=
    fun s => List.decidableBEx _ links
  exact List.decidableBAll _ sources

theorem cover_sound {n m a k : Nat} (d : Dictionary n m a)
    (rules : Fin k → Support n) (sources targets : List (Fin m))
    (links : List (Link m k)) (covered : CoverCheck sources targets links)
    (positive : ∀ r, 0 < d.denominators r)
    (rules_checked : ∀ i, (rules i).Check d.rows)
    (links_checked : ∀ w ∈ links, w.Check d rules)
    (q : S12Pilot.OpenSquare) (h : OrientedPoseCovered (sources.map d.pose) q) :
    OrientedPoseCovered (targets.map d.pose) q := by
  obtain ⟨pose, hp, hq⟩ := h
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hp
  obtain ⟨w, hw, he, ht⟩ := covered s hs
  refine ⟨d.pose w.target, List.mem_map.mpr ⟨w.target, ht, rfl⟩, ?_⟩
  apply w.sound d rules (links_checked w hw) positive rules_checked q
  simpa only [he] using hq

#print axioms Link.sound
#print axioms cover_sound

end N12Compact.IndexedRelaxation
