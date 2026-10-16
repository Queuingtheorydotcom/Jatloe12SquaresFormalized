import Compact.Geometry.WallStrongerLowerReach
import Compact.Bridge.C977CentralReach
import Completion.Cases.C977.MissingCornerPoints

/-! Original missing-corner strengthening pushes the actual bottom
wall to (2.6,1). Both foreign exclusions are supplied by their genuine
singleton/central owners. No square-frame sign is assumed. -/
namespace N12Compact.C977BottomExtendedReach

open S12 S12Pilot S12Completion.C977
set_option Elab.async false

theorem point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1) :
    (p.square (orderedOwner p 9)).Inside (13/5) 1 := by
  let D := p.square (orderedOwner p 9)
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have marker : D.Inside 2 (457/500) := by
    have point := (dm 13).mpr (by decide)
    simpa [D,Owns,marker] using point
  have high : D.Inside (12/5) 1 := by
    have check : ∀ owned∈pruningDomain4 9, 6∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 9)
    have point := (nat_combined_exact p (orderedOwner p 9) 6 (by decide)).mpr owned
    simpa [D,auxPoints,fPoints,gPoints] using point
  have stronger := code_one_missing_points p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0) missingCorner
  have central := (C977CentralReach.central_points p hf).1
  have missingLow : ¬D.Inside (91/50) 1 := fun h => p.disjoint _ _
    (fun eq => (by decide : (9 : Fin 12)≠0) (ordered_owner_injective p hf eq)) _ _
    ⟨h,stronger.horizontal_point⟩
  have missingInward : ¬D.Inside 2 (3/2) := fun h => p.disjoint _ _
    (fun eq => (by decide : (9 : Fin 12)≠5) (ordered_owner_injective p hf eq)) _ _
    ⟨h,central⟩
  have side : 1<(pullSwap D).side := by
    change 1<(p.square (orderedOwner p 9)).side
    rw [p.congruent]
    exact p.side_gt_one
  have box : InsideContainer (pullSwap D) := by
    intro x y h
    have point := (inside_pullSwap D x y).mp h
    have contained := p.contained (orderedOwner p 9) y x point
    exact ⟨contained.2.2.1,contained.2.2.2,contained.1,contained.2.1⟩
  have result := WallStrongerLowerReach.point (pullSwap D) side box
    ((inside_pullSwap D _ _).mpr marker) ((inside_pullSwap D _ _).mpr high)
    (fun h => missingLow ((inside_pullSwap D _ _).mp h))
    (fun h => missingInward ((inside_pullSwap D _ _).mp h))
  exact (inside_pullSwap D 1 (13/5)).mp result

#print axioms point
end N12Compact.C977BottomExtendedReach
