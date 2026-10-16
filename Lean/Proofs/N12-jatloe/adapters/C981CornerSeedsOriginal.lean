import Completion.Cases.C981.Geometry
import S12.MissingCornerBranches

/-! Retained original stronger corner-seed theorem. Its missing original helpers are
recorded in evidence/c981-catalogue-dependency-factor.json; this is an unresolved
draft root, not an assumption used by the catalogue or a claimed checked theorem. -/
namespace S12Completion.C981
open S12 S12Pilot

/-- A complete split at the corner point forces an additional pair of strict
interior seed points in at least one singleton owner. The second branch
includes every configuration where the first owner contains the corner point;
the first branch also includes configurations where neither owner does. -/
theorem corner_seed_split (p : NormalizedPacking)
    (hf : codedMarkerFamily p = family) :
    ∃ i j : Fin 12, i ≠ j ∧
      ExactMarkers (p.square i) {0} ∧ ExactMarkers (p.square j) {1} ∧
      (((p.square i).Inside (91 / 50) 1 ∧
        (p.square i).Inside (49 / 25) (19 / 25)) ∨
       ((p.square j).Inside 1 (91 / 50) ∧
        (p.square j).Inside (19 / 25) (49 / 25))) := by
  obtain ⟨i, j, hij, _, _, hi, hj⟩ := corner_owners p hf
  refine ⟨i, j, hij, hi, hj, ?_⟩
  rcases disjoint_corner_split (p.square i) (p.square j) 1 1
      (p.disjoint i j hij) with hmiss | ⟨_, hmiss⟩
  · left
    exact singleton_zero_missing_points (p.square i)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained i) hi hmiss
  · right
    exact singleton_one_missing_points (p.square j)
      (by rw [p.congruent]; exact p.side_gt_one)
      (by rw [p.congruent]; exact p.side_le) (p.contained j) hj hmiss


end S12Completion.C981
