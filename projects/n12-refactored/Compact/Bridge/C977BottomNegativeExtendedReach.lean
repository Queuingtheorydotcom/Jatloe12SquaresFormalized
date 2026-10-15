import Compact.Geometry.WallDiagonalFarReach
import Compact.Bridge.C977BottomExtendedReach

/-! The actual strengthened bottom singleton and central crosspoint
push every nonpositive canonical frame of owner 9 to (2.86,1).
The original missing-corner root is retained without reflection. -/
namespace N12Compact.C977BottomNegativeExtendedReach

open S12 S12Pilot S12Completion.C977 C977CornerCubic
set_option Elab.async false

private noncomputable def swapFrame (q : OpenSquare) : OpenSquare where
  c := q.c
  s := -q.s
  loU := q.loV
  loV := q.loU
  side := q.side
  unit_normal := by nlinarith only [q.unit_normal]
  side_pos := q.side_pos

private theorem inside_swapFrame (q : OpenSquare) (x y : ℝ) :
    (swapFrame q).Inside x y↔q.Inside y x := by
  dsimp [swapFrame,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;>
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d]

theorem frame_point (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (D : OpenSquare) (t : ℝ) (signed : D.s=-t) (normal : Normal D.c t)
    (shape : D.side=(p.square (orderedOwner p 9)).side)
    (equivalent : ∀ x y, D.Inside x y↔(p.square (orderedOwner p 9)).Inside x y)
    (missingCorner : ¬(p.square (orderedOwner p 0)).Inside 1 1) :
    D.Inside (143/50) 1 := by
  have dm := coded_exact p (orderedOwner p 9)
  rw [ordered_owner_code p hf 9] at dm
  have marker : D.Inside 2 (457/500) := (equivalent _ _).mpr (by
    have point := (dm 13).mpr (by decide)
    simpa [Owns,marker] using point)
  have high : D.Inside (12/5) 1 := (equivalent _ _).mpr (by
    have check : ∀ owned∈pruningDomain4 9, 6∈owned := by decide
    have owned := check _ (pruned_auxiliary_domain_actual p hf 9)
    have point := (nat_combined_exact p (orderedOwner p 9) 6 (by decide)).mpr owned
    simpa [auxPoints,fPoints,gPoints] using point)
  have stronger := code_one_missing_points p (orderedOwner p 0)
    (by simpa [auxiliaryCode] using ordered_owner_code p hf 0) missingCorner
  have central := (C977CentralReach.central_points p hf).1
  have missingFar : ¬D.Inside (49/25) (19/25) := fun h => p.disjoint _ _
    (fun eq => (by decide : (9 : Fin 12)≠0) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent _ _).mp h,stronger.lower_point⟩
  have missingInward : ¬D.Inside 2 (3/2) := fun h => p.disjoint _ _
    (fun eq => (by decide : (9 : Fin 12)≠5) (ordered_owner_injective p hf eq)) _ _
    ⟨(equivalent _ _).mp h,central⟩
  have swappedNormal : Normal (swapFrame D).c (swapFrame D).s := by
    simpa only [swapFrame,signed,neg_neg] using normal
  have side : 1<(swapFrame D).side := by
    change 1<D.side
    rw [shape,p.congruent]
    exact p.side_gt_one
  have box : InsideContainer (swapFrame D) := by
    intro x y h
    have point := (equivalent y x).mp ((inside_swapFrame D x y).mp h)
    have contained := p.contained (orderedOwner p 9) y x point
    exact ⟨contained.2.2.1,contained.2.2.2,contained.1,contained.2.1⟩
  have result := WallDiagonalFarReach.point (swapFrame D) swappedNormal side box
    ((inside_swapFrame D _ _).mpr marker) ((inside_swapFrame D _ _).mpr high)
    (fun h => missingFar ((inside_swapFrame D _ _).mp h))
    (fun h => missingInward ((inside_swapFrame D _ _).mp h))
  exact (inside_swapFrame D 1 (143/50)).mp result

#print axioms frame_point
end N12Compact.C977BottomNegativeExtendedReach
