import Compact.Cases.C898.ChordFusedGeometry

/-! One direct outgoing hull per original angle.  Every row is proved from
the original source and the two simultaneous strict cuts.  No old chord
piece or relaxation-link identifier is used in this interface. -/

namespace N12Compact.C898Chord.Fused
open S12 S12Pilot C898Shared IntegerSupport CoordinateBound

noncomputable def cutRow (source : Fin poseCount) (index : Nat) : Row :=
  ((cutRows source)[index]?).getD RowSupport.one

theorem cutRow_holds (source : Fin poseCount) (index : Nat) (p : Fin 2 → ℝ)
    (holds : ∀ row ∈ cutRows source, row.Holds p) : (cutRow source index).Holds p := by
  cases entry : (cutRows source)[index]? with
  | none => simpa only [cutRow, entry, Option.getD_none] using RowSupport.one_holds p
  | some row =>
      simpa only [cutRow, entry, Option.getD_some] using
        holds row (List.mem_of_getElem? entry)

structure DirectSupport where
  target : Fin rowCount
  left : Nat
  right : Nat
  deriving DecidableEq

def DirectSupport.Check (support : DirectSupport) (source : Fin poseCount) : Prop :=
  RowSupport.Check (cutRow source support.left) (cutRow source support.right)
    (rows support.target)

noncomputable instance (support : DirectSupport) (source : Fin poseCount) :
    Decidable (support.Check source) := inferInstanceAs (Decidable (RowSupport.Check _ _ _))

structure DirectPlan where
  source : Fin poseCount
  target : Option (Fin poseCount)
  supports : List DirectSupport
  closeLeft : Nat
  closeRight : Nat
  deriving DecidableEq

def DirectPlan.Check (plan : DirectPlan) : Prop :=
  match plan.target with
  | none => RowSupport.Check (cutRow plan.source plan.closeLeft)
      (cutRow plan.source plan.closeRight)
      (upper (leftHi + (poseRadius plan.source).radius) false)
  | some target => poseAngle plan.source = poseAngle target ∧
      ∀ r ∈ poseRows target, r ∈ poseRows plan.source ∨
        ∃ support ∈ plan.supports, support.target = r ∧ support.Check plan.source

noncomputable instance (plan : DirectPlan) : Decidable plan.Check := by
  unfold DirectPlan.Check
  cases plan.target with
  | none => infer_instance
  | some target =>
      letI : DecidablePred (fun r => r ∈ poseRows plan.source ∨
          ∃ support ∈ plan.supports, support.target = r ∧ support.Check plan.source) :=
        fun r => by
          letI : Decidable (∃ support ∈ plan.supports,
              support.target = r ∧ support.Check plan.source) :=
            List.decidableBEx _ plan.supports
          infer_instance
      letI : Decidable (∀ r ∈ poseRows target, r ∈ poseRows plan.source ∨
          ∃ support ∈ plan.supports, support.target = r ∧ support.Check plan.source) :=
        List.decidableBAll _ (poseRows target)
      infer_instance

theorem DirectPlan.sound (plan : DirectPlan) (checked : plan.Check)
    (q : OpenSquare) (hs : (poses plan.source).OrientedRealizes q)
    (lo : ((leftHi + (poseRadius plan.source).radius : ℚ) : ℝ) < centerX q)
    (hi : centerX q < ((rightLo - (poseRadius plan.source).radius : ℚ) : ℝ)) :
    ∃ target, plan.target = some target ∧ (poses target).OrientedRealizes q := by
  cases selected : plan.target with
  | none =>
      have hc : RowSupport.Check (cutRow plan.source plan.closeLeft)
          (cutRow plan.source plan.closeRight)
          (upper (leftHi + (poseRadius plan.source).radius) false) := by
        simpa only [DirectPlan.Check, selected] using checked
      have bound := (holds_upper _ false _).mp (RowSupport.sound hc _
        (cutRow_holds _ _ _ (cutRows_hold _ q hs lo hi))
        (cutRow_holds _ _ _ (cutRows_hold _ q hs lo hi)))
      exact ((not_lt_of_ge bound) lo).elim
  | some target =>
      have hc : poseAngle plan.source = poseAngle target ∧
          ∀ r ∈ poseRows target, r ∈ poseRows plan.source ∨
            ∃ support ∈ plan.supports, support.target = r ∧ support.Check plan.source := by
        simpa only [DirectPlan.Check, selected] using checked
      refine ⟨target, by simp only [selected], ?_⟩
      apply dictionary.transfer hc.1 positive_denominators q hs
      intro r hr
      change (rows r).Holds ![centerX q, centerY q]
      rcases hc.2 r hr with old | ⟨support, _, target_eq, support_checked⟩
      · exact pose_row_holds hs r old
      · rw [← target_eq]
        exact RowSupport.sound support_checked _
          (cutRow_holds _ _ _ (cutRows_hold _ q hs lo hi))
          (cutRow_holds _ _ _ (cutRows_hold _ q hs lo hi))

def DirectCoverCheck (sources targets : List (Fin poseCount))
    (plans : List DirectPlan) : Prop :=
  ∀ source ∈ sources, ∃ plan ∈ plans, plan.source = source ∧
    match plan.target with
    | none => True
    | some target => target ∈ targets

instance (sources targets : List (Fin poseCount)) (plans : List DirectPlan) :
    Decidable (DirectCoverCheck sources targets plans) := by
  unfold DirectCoverCheck
  letI : DecidablePred (fun source => ∃ plan ∈ plans, plan.source = source ∧
      match plan.target with | none => True | some target => target ∈ targets) :=
    fun source => by
      letI : DecidablePred (fun plan : DirectPlan => plan.source = source ∧
          match plan.target with | none => True | some target => target ∈ targets) :=
        fun plan => by
          dsimp only
          cases h : plan.target <;> simp only [h] <;> infer_instance
      exact List.decidableBEx _ plans
  exact List.decidableBAll _ sources

theorem direct_cover (sources targets : List (Fin poseCount)) (plans : List DirectPlan)
    (covered : DirectCoverCheck sources targets plans)
    (checked : ∀ plan ∈ plans, plan.Check) (q : OpenSquare)
    (hs : OrientedPoseCovered (sources.map poses) q)
    (cuts : ∀ source ∈ sources, (poses source).OrientedRealizes q →
      ((leftHi + (poseRadius source).radius : ℚ) : ℝ) < centerX q ∧
        centerX q < ((rightLo - (poseRadius source).radius : ℚ) : ℝ)) :
    OrientedPoseCovered (targets.map poses) q := by
  obtain ⟨pose, hp, hs⟩ := hs
  obtain ⟨source, hm, rfl⟩ := List.mem_map.mp hp
  obtain ⟨plan, hplan, source_eq, target_mem⟩ := covered source hm
  have hh := cuts source hm hs
  obtain ⟨target, ht, hq⟩ := plan.sound (checked plan hplan) q
    (by simpa only [source_eq] using hs)
    (by simpa only [source_eq] using hh.1) (by simpa only [source_eq] using hh.2)
  exact ⟨poses target,
    List.mem_map.mpr ⟨target, by simpa only [ht] using target_mem, rfl⟩, hq⟩

#print axioms direct_cover
end N12Compact.C898Chord.Fused
