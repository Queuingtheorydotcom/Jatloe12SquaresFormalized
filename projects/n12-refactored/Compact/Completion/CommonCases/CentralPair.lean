import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.OutwardPoint
import Compact.Completion.C981.OutwardAnchor

/-! The complete local inward/mixed-or-outward ending. All exclusions and
the one complete top segment must still be supplied by original owners. -/
namespace N12Compact.CommonCases.CentralPair
open S12 S12Pilot
set_option Elab.async false

theorem impossible (a n : OpenSquare) (sideA : 1 < a.side) (sideN : 1 < n.side)
    (markerA : a.Inside (47/20) (33/20))
    (inwardA : a.Inside 2 (87/50)) (elbowA : a.Inside (113/50) 2)
    (missingSW : ¬a.Inside (33/20) (33/20))
    (missingBottom : ¬a.Inside (12/5) 1)
    (markerN : n.Inside (47/20) (47/20))
    (pairN : (n.Inside 2 (113/50) ∧ n.Inside 3 (12/5)) ∨
      (n.Inside 3 (113/50) ∧ n.Inside 3 (12/5)))
    (missingR : ¬n.Inside (1543/500) 2)
    (missingP : ¬n.Inside 3 3)
    (missingH : ¬n.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → ¬n.Inside z 3)
    (apart : ∀ x y, ¬(a.Inside x y ∧ n.Inside x y)) : False := by
  have missingNE : ¬a.Inside (47/20) (47/20) :=
    fun h => apart _ _ ⟨h,markerN⟩
  have missingG : ¬n.Inside (113/50) 2 := fun h => apart _ _ ⟨elbowA,h⟩
  rcases pairN with mixed | outward
  · apply C981CompletionOutwardAnchor.impossible (pullY n) sideN
    · norm_num [inside_pullY]; exact markerN
    · norm_num [inside_pullY]; exact mixed.1
    · norm_num [inside_pullY]; exact mixed.2
    · norm_num [inside_pullY]; exact missingP
    · norm_num [inside_pullY]; exact missingR
    · norm_num [inside_pullY]; exact missingG
    · intro z low high own
      exact avoid z low high (by norm_num [inside_pullY] at own; exact own)
  · have first := InwardPoint.point_original a sideA markerA inwardA elbowA
      missingSW missingNE missingBottom
    have second := OutwardPoint.point_original n sideN markerN outward.1 outward.2
      missingG missingR missingP missingH avoid
    exact apart _ _ ⟨first,second⟩

#print axioms impossible
end N12Compact.CommonCases.CentralPair
