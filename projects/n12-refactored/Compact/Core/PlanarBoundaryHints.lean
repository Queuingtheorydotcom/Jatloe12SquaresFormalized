import Compact.Core.PlanarBoundaryFilter

/-! Checked boundary hints with a literal cache of the retained rows.

The hint producer is deliberately outside the proof. The original filter
checker verifies every omitted line, and a separate equality verifies the
complete retained list. Neither proof replays unsuccessful hint searches.
-/

namespace N12Compact.PlanarBoundaryHints
open IntegerSupport PlanarVertexCheck PlanarVertexSparse PlanarBoundaryFilter

structure Cache (base : List Row) (forbidden : List (List Row)) where
  plan : List (Option LineExclusion)
  plan_checked : FilterCheck base ((base ++ forbidden.flatten).dedup) plan
  rows : List Row
  rows_exact : rows = active ((base ++ forbidden.flatten).dedup) plan

/-- The same original continuous vertex obligation, with every discarded
boundary justified by the existing checked parallel-row inequality. -/
theorem Cache.toCheck {base : List Row} {forbidden : List (List Row)}
    {targets : List Row} (cache : Cache base forbidden)
    (checked : triangle (PairCheck base forbidden targets) cache.rows) :
    PlanarVertexCheck.Check base forbidden targets := by
  apply PlanarBoundaryFilter.Check.toCheck
  refine ⟨cache.plan_checked, ?_⟩
  simpa only [cache.rows_exact] using checked

#print axioms Cache.toCheck
end N12Compact.PlanarBoundaryHints
