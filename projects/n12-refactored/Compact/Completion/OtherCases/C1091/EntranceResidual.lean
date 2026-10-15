import Compact.Completion.OtherCases.C1091.EntranceAllPositive
import Compact.Completion.OtherCases.C1091.ResidualProduction
import Compact.Completion.OtherCases.C1089.SingletonCorner
import Compact.Completion.CommonCases.SingletonMissing

/-! C1091's actual residual-sector entrance. The stronger singleton
seeds are derived only under its genuine missing-corner assumption.
Only the northwest F3 producer remains open in this sector. Source only. -/
namespace N12Compact.Completion.OtherCases.C1091.EntranceResidual
open S12 S12Pilot OriginalData EntranceFrame EntranceWalls
set_option Elab.async false
noncomputable section

abbrev clockwise_pair := C1089.SectorEntrances.clockwise_pair

theorem northeast_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 6).Inside 3 (113/50) ∧ (owners p 6).Inside 3 (12/5) := by
  let h := frame p hf
  have se := southeast_inward p hf right
  have g9 : (owners p 6).Inside 3 (12/5) := by
    rcases EntranceDomains.northeast_g p hf with own | own | own
    · exact False.elim (h.apart 6 5 (by decide) _ _ ⟨own,se.2⟩)
    · exact False.elim (h.apart 6 11 (by decide) _ _
        ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    · exact own
  have fc := EntranceDomains.northeast_f p hf
  have result := clockwise_pair (pullSwap (owners p 6)) (h.side 6)
    (by norm_num [inside_pullSwap]; exact h.northeastMarker)
    (by norm_num [inside_pullSwap]; exact g9)
    (by norm_num [inside_pullSwap]; tauto)
    (by norm_num [inside_pullSwap]; exact fun own =>
      h.apart 6 5 (by decide) _ _ ⟨own,se.2⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 11 (by decide) _ _
      ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own => h.apart 6 11 (by decide) _ _
      ⟨own,top_high p hf top _ (by norm_num) (by norm_num)⟩)
    (by norm_num [inside_pullSwap]; exact fun own =>
      h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
  norm_num [inside_pullSwap] at result
  exact ⟨result,g9⟩


theorem right_pair (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 10).Inside 3 (87/50) ∧ (owners p 10).Inside 3 (8/5) :=
  DirectDomains.right_pair p hf (northeast_pair p hf right top).1

theorem southeast_south (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 5).Inside 2 (3/2) := by
  let h := frame p hf
  have se := southeast_inward p hf right
  have ne := northeast_pair p hf right top
  have r := right_pair p hf right top
  have low := C1089.WallOrigins.right_low (owners p) (h.side 10) (h.box 10) h.apart
    h.rightMarker r.2 ne.1 h.southeastMarker
  have middle : (owners p 10).Inside 3 (3/2) := by
    convert inside_segment (owners p 10) 3 (36/25) 3 (8/5) (3/8)
      low r.2 (by norm_num) (by norm_num) using 1 <;> norm_num
  have point := C981CompletionCrosspoint.point (pullY (owners p 5)) (h.side 5)
    (by norm_num [inside_pullY]; exact se.1)
    (by norm_num [inside_pullY]; exact se.2)
    (by norm_num [inside_pullY]; exact h.southeastMarker)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 6 (by decide) _ _ ⟨own,h.northeastMarker⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 4 (by decide) _ _ ⟨own,h.southwestMarker⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 10 (by decide) _ _ ⟨own,r.2⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 10 (by decide) _ _ ⟨own,middle⟩)
  norm_num [inside_pullY] at point
  exact point

theorem stronger_singleton_seeds (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (missing : ¬(owners p 0).Inside 1 1) :
    (owners p 0).Inside (91/50) 1 ∧ (owners p 0).Inside (49/25) (19/25) := by
  have exactMarkers : ExactMarkers (owners p 0) (maskSupport 1) := by
    have code := CommonCases.OriginalOwners.code family p hf 1 (by decide +kernel)
    change ExactMarkers (p.square (ownerIndex p 1)) (maskSupport 1)
    simpa only [code] using coded_exact p (ownerIndex p 1)
  have support : maskSupport 1=({0} : Finset Marker) := by decide +kernel
  rw [support] at exactMarkers
  exact CommonCases.SingletonMissing.zero_missing_points _ (side p 0)
    (cap p 0) (box p 0) exactMarkers missing

/-- The real Q0 singleton corner is derived, rather than supplied as a
post-reduction assumption. The old unavailable singleton imports are absent. -/
theorem singleton_corner (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11)) :
    (owners p 0).Inside 1 1 := by
  let h := frame p hf
  by_contra missing
  have strong := stronger_singleton_seeds p hf missing
  exact missing (C1089.SingletonCorner.corner_of_seeds (owners p)
    h.side h.same h.box h.apart h.singletonMarker strong.1 strong.2
    h.southeastCornerBottom h.southeastCorner h.southeastMarker
    (southeast_south p hf right top) (northeast_pair p hf right top).1
    h.bottomMarker (EntranceDomains.bottom_far p hf)
    (EntranceDomains.bottom_bar p hf).2.1 h.rightMarker (right_pair p hf right top).2)

/-- Five of the six old residual entry points now have actual producers;
this join isolates only Q7's F3 point, without strengthening its statement. -/
theorem input_of_northwest (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11))
    (northwest : (owners p 7).Inside (8/5) 3) : ResidualEntrance (owners p) where
  cornerSW := singleton_corner p hf right top
  mergedLow := EntranceMergedLow.original p hf
  southeastF4 := (southeast_inward p hf right).1
  southeastG6 := (southeast_inward p hf right).2
  northeastF9 := (northeast_pair p hf right top).1
  northwestF3 := northwest

theorem impossible_of_northwest (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (right : centerY (owners p 10)≤2) (top : 2≤centerX (owners p 11))
    (northwest : (owners p 7).Inside (8/5) 3) : False :=
  impossible_of_residual_entrance p hf (input_of_northwest p hf right top northwest)

end
#print axioms northeast_pair
end N12Compact.Completion.OtherCases.C1091.EntranceResidual
