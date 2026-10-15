import Compact.Cases.C868.UpperNegativeOutwardEnding

/-! Consequences of the surviving top-marker upper-face alternative.
Both southeast points are produced by the same actual outward square.
No point is moved to a different owner and every face exit stays weak. -/
namespace N12Compact.C868.UpperNegativeCap
open S12 S12Pilot C977CornerCubic MergedPending.NegativeUpperFaces
set_option Elab.async false

theorem sharp_upper (H : OpenSquare) (h : Input H)
    (cap : H.loV+H.side≤(543/500)*H.c)
    (missing : ¬H.Inside (21/40) (1/8)) :
    H.loU+H.side≤(21/40)*H.c+(1/8)*H.s := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have floor := lower_v H h
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.northeast.1,cp,h.normal.1]
  · linarith only [high]
  · linarith only [cap,h.side,bounds.2.1,h.normal.1]
  · linarith only [floor,h.side,bounds.2.1,bounds.2.2.2.1]

theorem lower_tilt (H : OpenSquare) (h : Input H)
    (upper : H.loU+H.side≤(21/40)*H.c+(1/8)*H.s) :
    H.c< -5*H.s := by
  have floor := lower_u H h
  have bounds := normal_bounds h.normal
  have span : 1<(157/200)*H.c-(7/8)*H.s := by
    linarith only [h.side,floor,upper]
  apply lt_of_not_ge
  intro shallow
  linarith only [span,shallow,bounds.2.1]

theorem near_upper (H : OpenSquare) (h : Input H)
    (cap : H.loV+H.side≤(543/500)*H.c)
    (tilt : H.c< -5*H.s)
    (missing : ¬H.Inside (23/50) (1/100)) :
    H.loU+H.side≤(23/50)*H.c+(1/100)*H.s := by
  have bounds := normal_bounds h.normal
  have cp : 0<H.c := by linarith only [bounds.1]
  have floor := lower_v H h
  apply le_of_not_gt
  intro high
  apply missing
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [h.northeast.1,cp,h.normal.1]
  · linarith only [high]
  · linarith only [cap,h.side,tilt,bounds.2.1]
  · linarith only [floor,h.side,bounds.2.1,bounds.2.2.2.1]

theorem span (H : OpenSquare) (h : Input H)
    (upper : H.loU+H.side≤(23/50)*H.c+(1/100)*H.s) :
    1<(18/25)*H.c-(99/100)*H.s := by
  have floor := lower_u H h
  linarith only [h.side,floor,upper]

end N12Compact.C868.UpperNegativeCap

namespace N12Compact.C868
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

/-- The same physical H inherits both southeast upper-face caps. -/
theorem negative_upper_southeast_caps (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (H : OpenSquare)
    (normal : Normal H.c (-H.s))
    (shape : H.side=(owner p 3072).side)
    (inside : ∀ x y,H.Inside x y↔(owner p 3072).Inside x y) :
    (H.translated 2 2).loU+H.side≤(21/40)*H.c+(1/8)*H.s ∧
    (H.translated 2 2).loU+H.side≤(23/50)*H.c+(1/100)*H.s ∧
    1<(18/25)*H.c-(99/100)*H.s := by
  have input := negative_upper_input p hf H normal shape inside
  have cap := negative_upper_top_cap p hf H normal shape inside
  have points := southeast_outward_points p hf (southeast_outward_required p hf)
  have sharpMissing : ¬(H.translated 2 2).Inside (21/40) (1/8) := by
    norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,points.2⟩
  have nearMissing : ¬(H.translated 2 2).Inside (23/50) (1/100) := by
    norm_num only [inside_translated_iff]
    intro own
    exact apart p hf 3072 512 (by decide +kernel) (by decide +kernel) (by decide +kernel)
      _ _ ⟨(inside _ _).mp own,points.1⟩
  have sharp := UpperNegativeCap.sharp_upper (H.translated 2 2) input cap sharpMissing
  have tilt := UpperNegativeCap.lower_tilt (H.translated 2 2) input sharp
  have near := UpperNegativeCap.near_upper (H.translated 2 2) input cap tilt nearMissing
  exact ⟨sharp,near,UpperNegativeCap.span (H.translated 2 2) input near⟩

#print axioms UpperNegativeCap.sharp_upper
#print axioms UpperNegativeCap.near_upper
#print axioms negative_upper_southeast_caps
end N12Compact.C868
