import Compact.Cases.C898.ChordFusedPlans

/-! Materialize a plan's exact rows once. Arithmetic checks then see only
small literal integers, while `toCheck` retains the original semantic API. -/

namespace N12Compact.C898Chord.Fused
open C898Shared IntegerSupport CoordinateBound

def cachedRow (inputs : List Row) (index : Nat) : Row :=
  (inputs[index]?).getD RowSupport.one

structure PlanCache where
  inputs : List Row
  supports : List (DirectSupport × Row)
  closing : Row

def PlanCache.Exact (cache : PlanCache) (plan : DirectPlan) : Prop :=
  cache.inputs = cutRows plan.source ∧
  cache.supports.map Prod.fst = plan.supports ∧
  (∀ entry ∈ cache.supports, rows entry.1.target = entry.2) ∧
  cache.closing = upper (leftHi + (poseRadius plan.source).radius) false

def DirectPlan.Shape (plan : DirectPlan) : Prop :=
  match plan.target with
  | none => True
  | some target => poseAngle plan.source = poseAngle target ∧
      ∀ r ∈ poseRows target, r ∈ poseRows plan.source ∨
        ∃ support ∈ plan.supports, support.target = r

def PlanCache.Numeric (cache : PlanCache) (plan : DirectPlan) : Prop :=
  match plan.target with
  | none => RowSupport.Check (cachedRow cache.inputs plan.closeLeft)
      (cachedRow cache.inputs plan.closeRight) cache.closing
  | some _ => ∀ entry ∈ cache.supports,
      RowSupport.Check (cachedRow cache.inputs entry.1.left)
        (cachedRow cache.inputs entry.1.right) entry.2

noncomputable instance (cache : PlanCache) (plan : DirectPlan) :
    Decidable (cache.Exact plan) := by
  unfold PlanCache.Exact
  letI : Decidable (∀ entry ∈ cache.supports, rows entry.1.target = entry.2) :=
    List.decidableBAll _ cache.supports
  infer_instance

noncomputable instance (plan : DirectPlan) : Decidable plan.Shape := by
  unfold DirectPlan.Shape
  cases plan.target with
  | none => infer_instance
  | some target =>
      letI : DecidablePred (fun r => r ∈ poseRows plan.source ∨
          ∃ support ∈ plan.supports, support.target = r) := fun r => by
        letI : Decidable (∃ support ∈ plan.supports, support.target = r) :=
          List.decidableBEx _ plan.supports
        infer_instance
      letI : Decidable (∀ r ∈ poseRows target, r ∈ poseRows plan.source ∨
          ∃ support ∈ plan.supports, support.target = r) :=
        List.decidableBAll _ (poseRows target)
      infer_instance

instance (cache : PlanCache) (plan : DirectPlan) :
    Decidable (cache.Numeric plan) := by
  unfold PlanCache.Numeric
  cases plan.target with
  | none => infer_instance
  | some _ => exact List.decidableBAll _ cache.supports

theorem PlanCache.toCheck (cache : PlanCache) (plan : DirectPlan)
    (hcache : cache.Exact plan) (shape : plan.Shape)
    (numeric : cache.Numeric plan) : plan.Check := by
  have inputs (i : Nat) : cachedRow cache.inputs i = cutRow plan.source i := by
    unfold cachedRow cutRow
    rw [hcache.1]
  cases ht : plan.target with
  | none =>
      simp only [DirectPlan.Check,ht]
      simpa only [PlanCache.Numeric, ht, inputs, hcache.2.2.2] using numeric
  | some target =>
      have shape' : poseAngle plan.source = poseAngle target ∧
          ∀ r ∈ poseRows target, r ∈ poseRows plan.source ∨
            ∃ support ∈ plan.supports, support.target = r := by
        simpa only [DirectPlan.Shape,ht] using shape
      have numeric' : ∀ entry ∈ cache.supports,
          RowSupport.Check (cachedRow cache.inputs entry.1.left)
            (cachedRow cache.inputs entry.1.right) entry.2 := by
        simpa only [PlanCache.Numeric,ht] using numeric
      simp only [DirectPlan.Check,ht]
      refine ⟨shape'.1, ?_⟩
      intro r hr
      rcases shape'.2 r hr with old | ⟨support,member,target_eq⟩
      · exact Or.inl old
      · have mapped : support ∈ cache.supports.map Prod.fst := by
          rw [hcache.2.1]
          exact member
        obtain ⟨entry,entry_mem,entry_eq⟩ := List.mem_map.mp mapped
        refine Or.inr ⟨support,member,target_eq,?_⟩
        rw [← entry_eq]
        unfold DirectSupport.Check
        rw [hcache.2.2.1 entry entry_mem]
        simpa only [inputs] using numeric' entry entry_mem

#print axioms PlanCache.toCheck
end N12Compact.C898Chord.Fused
