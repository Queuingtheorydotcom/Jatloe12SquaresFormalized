import Compact.Completion.OtherCases.C983.C974SingletonAngle
import Compact.Completion.OtherCases.C983.C974ReducedEnding

/-! Full local Theorem 1 of C974-THREE-SQUARE-ENDING, now joined to
the written sign and angle prerequisites. Actual C983 adapters below
retain the literal stronger singleton seeds: their historical source
chain is absent, so no whole C983 exclusion is asserted.
All new prerequisite modules are source-only and uncompiled. -/
namespace N12Compact.Completion.OtherCases.C983.C974LocalEnding
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem impossible (K W C : OpenSquare) (raw : C974LocalData.Input K W C) : False := by
  have pair := C974MissingCorner.Input.of_local raw
  obtain ⟨A,B,ashape,bshape,asame,bsame,apos,acanonical,bpos,bcanonical⟩ :=
    C974MissingCorner.positive_frames K W pair
  have framed := (pair.reframeK ashape asame).reframeW bshape bsame
  have reduced := C974MissingCorner.reduced_input A B framed apos acanonical bpos bcanonical
  apply C974ReducedEnding.impossible A B C reduced ((bsame _ _).mpr raw.farW)
    (bshape.trans (raw.sameKW.symm.trans raw.sameKC)) raw.cornerWalls raw.corner raw.missingCorner
  intro x y both
  exact raw.apartWC x y ⟨(bsame x y).mp both.1,both.2⟩

/-- Original bottom missing-corner root with the retained stronger seed
and both actual midpoint conclusions stated explicitly. -/
theorem bottom_missing_corner_excluded_of_seeds (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 0).Inside 1 1)
    (seedA : (owners p 0).Inside (91/50) 1)
    (seedS : (owners p 0).Inside (49/25) (19/25))
    (origin : (owners p 9).Inside 2 1)
    (middle : ¬(owners p 9).Inside 2 (3/2))
    (outer : (owners p 5).Inside 3 (3/2)) : False :=
  impossible _ _ _ (C974LocalData.bottom_input p hf missing seedA seedS origin middle outer)

/-- The coordinate-exchanged actual-owner root, with its own two strict
stronger singleton seed premises, rather than a substituted seed owner. -/
theorem left_missing_corner_excluded_of_seeds (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7)
    (missing : ¬(owners p 1).Inside 1 1)
    (seedA : (owners p 1).Inside 1 (91/50))
    (seedS : (owners p 1).Inside (19/25) (49/25)) : False :=
  impossible _ _ _ (C974LocalData.left_input p hf f4 missing seedA seedS)

end
#print axioms impossible
#print axioms bottom_missing_corner_excluded_of_seeds
#print axioms left_missing_corner_excluded_of_seeds
end N12Compact.Completion.OtherCases.C983.C974LocalEnding
