import Compact.Geometry.SegmentCorner

/-! A segment moving from only the lower-U exit to only the lower-V
exit lies below the lower corner. Equality retains vertex contact. -/
namespace N12Compact.CommonCases.LowerSegmentSupport
set_option Elab.async false

theorem support (lU hU lV hV u0 v0 u1 v1 : ℝ)
    (hu0 : u0 ≤ lU) (hu1 : lU < u1) (hu2 : u1 < hU)
    (hv0 : lV < v0) (hv1 : v0 < hV) (hv2 : v1 ≤ lV)
    (avoid : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ¬(lU < (1-t)*u0+t*u1 ∧ (1-t)*u0+t*u1 < hU ∧
        lV < (1-t)*v0+t*v1 ∧ (1-t)*v0+t*v1 < hV)) :
    (v0-v1)*u0+(u1-u0)*v0 ≤ (v0-v1)*lU+(u1-u0)*lV := by
  have crossing := SegmentCorner.crossing_order lU hU (-hV) (-lV)
    u0 (-v0) u1 (-v1) hu0 hu1 hu2
    (by linarith only [hv1]) (by linarith only [hv0]) (by linarith only [hv2])
    (by
      intro t tn tu own
      apply avoid t tn tu
      refine ⟨own.1,own.2.1,?_,?_⟩ <;> nlinarith only [own.2.2.1,own.2.2.2])
  nlinarith only [crossing]

end N12Compact.CommonCases.LowerSegmentSupport
