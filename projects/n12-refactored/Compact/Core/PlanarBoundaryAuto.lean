import Compact.Core.PlanarBoundaryFilter

/-! Discover whole-line exclusions from the small original base.  The search
is checked once by the kernel and its result may be materialized as an active
boundary list.  No per-boundary witness table is part of the case data. -/

set_option Elab.async false

namespace N12Compact.PlanarBoundaryAuto

open IntegerSupport PlanarVertexCheck PlanarVertexSparse PlanarBoundaryFilter

/-- Clear the nonzero boundary pivot with a positive scale.  Discovery checks
the complete certificate, so a zero normal simply produces no exclusion. -/
def candidate (index : Nat) (row boundary : Row) : LineExclusion :=
  if boundary.x = 0 then
    ⟨index, |boundary.y|, if 0 ≤ boundary.y then row.y else -row.y⟩
  else
    ⟨index, |boundary.x|, if 0 ≤ boundary.x then row.x else -row.x⟩

def scan (base : List Row) (boundary : Row) : List Nat → Option LineExclusion
  | [] => none
  | index :: rest =>
      match base[index]? with
      | none => scan base boundary rest
      | some row =>
          let hint := candidate index row boundary
          if hint.Check base boundary then some hint else scan base boundary rest

theorem scan_sound (base : List Row) (boundary : Row) (indices : List Nat)
    (hint : LineExclusion) (found : scan base boundary indices = some hint) :
    hint.Check base boundary := by
  induction indices with
  | nil => cases found
  | cons index rest ih =>
      simp only [scan] at found
      cases entry : base[index]? with
      | none =>
          simp only [entry] at found
          exact ih found
      | some row =>
          simp only [entry] at found
          split_ifs at found with checked
          · cases found
            exact checked
          · exact ih found

def discover (base : List Row) (boundary : Row) : Option LineExclusion :=
  scan base boundary (List.range base.length)

theorem discover_sound (base : List Row) (boundary : Row)
    (hint : LineExclusion) (found : discover base boundary = some hint) :
    hint.Check base boundary :=
  scan_sound base boundary _ hint found

def plan (base : List Row) : List Row → List (Option LineExclusion)
  | [] => []
  | row :: rest => discover base row :: plan base rest

theorem plan_checked (base rows : List Row) : FilterCheck base rows (plan base rows) := by
  induction rows with
  | nil => trivial
  | cons row rest ih =>
      cases found : discover base row with
      | none => simpa only [plan, found, FilterCheck] using ih
      | some hint =>
          simpa only [plan, found, FilterCheck] using
            And.intro (discover_sound base row hint found) ih

def activeRows (base : List Row) (forbidden : List (List Row)) : List Row :=
  let boundaries := (base ++ forbidden.flatten).dedup
  active boundaries (plan base boundaries)

def Check (base : List Row) (forbidden : List (List Row)) (targets : List Row) : Prop :=
  triangle (PairCheck base forbidden targets) (activeRows base forbidden)

instance (base : List Row) (forbidden : List (List Row)) (targets : List Row) :
    Decidable (Check base forbidden targets) :=
  inferInstanceAs (Decidable (triangle _ _))

theorem Check.toCheck {base : List Row} {forbidden : List (List Row)}
    {targets : List Row} (checked : Check base forbidden targets) :
    PlanarVertexCheck.Check base forbidden targets :=
  PlanarBoundaryFilter.Check.toCheck ⟨plan_checked base _, checked⟩

/-- Numeric checking uses cached active rows; the discovery equality is
checked separately exactly once, rather than reduced at every pair. -/
theorem cached_toCheck {base : List Row} {forbidden : List (List Row)}
    {targets rows : List Row} (cached : rows = activeRows base forbidden)
    (checked : triangle (PairCheck base forbidden targets) rows) :
    PlanarVertexCheck.Check base forbidden targets := by
  apply Check.toCheck
  simpa only [Check, ← cached] using checked

#print axioms cached_toCheck
end N12Compact.PlanarBoundaryAuto
