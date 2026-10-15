import Compact.Completion.C1092.MPPMInwardPositiveNegativeSupport

/-! Complete local POSITIVE-MISSING-INWARD-ORIGIN-ENDING. The new
origin is only an explicit exclusion from C here; its actual foreign
owner is supplied by the original-family adapter. Both closed central
half-angle ranges, their common endpoint and weak contacts are included. -/
namespace N12Compact.C1092MPPMInwardPositive
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem origin_cap (C : OpenSquare) (h : Input C) (missing : ¬C.Inside (-1) 0) :
    C.loV+C.side≤C.s := by
  have p := profile C h
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [high,h.side,p.upperU,h.marker.2.1,h.crosspoint.2.2.1,
      cb.2.1,cp,p.positive,h.normal.2.1]

/-- No center/G/sign premise on the opposite central owner is used.
The additional origin is excluded from this same actual C. -/
theorem origin_impossible (C E : OpenSquare) (h : PairInput C E)
    (canonical : |E.s|≤E.c) (missing : ¬C.Inside (-1) 0) : False := by
  have p := profile C h.source
  have negative := successor_negative C E h canonical
  have en : Normal E.c (-E.s) :=
    ⟨by linarith only [negative],by simpa only [abs_of_neg negative] using canonical,
      by nlinarith only [E.unit_normal]⟩
  apply impossible_of_target C E h en
  by_cases small : half C.c C.s≤1/5
  · exact target_support_of_cap C E h en C.s (origin_cap C h.source missing)
      (NegativeScalars.small_target h.source.normal p.positive en small)
  · exact target_support_of_cap C E h en ((7/20)*(C.c+C.s)) p.upperV
      (NegativeScalars.marker_target h.source.normal en (le_of_lt (lt_of_not_ge small)) p.halfSmall.le)

end
#print axioms origin_cap
#print axioms origin_impossible
end N12Compact.C1092MPPMInwardPositive
