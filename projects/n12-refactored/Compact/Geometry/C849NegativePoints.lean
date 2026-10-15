import Compact.Geometry.C849PositiveAbove

/-! Exact consequences of the original negative-frame B triangle.
The inward point is uniform over the whole canonical negative arc, including
its diagonal endpoint. The strict owned marker is essential at that endpoint. -/
namespace N12Compact.C849NegativePoints
open S12 S12Pilot FourSquareAnchors

/-- The point occupied by A selects B's upper longitudinal face. -/
theorem upper_face (B : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (canonical : -B.s ≤ B.c)
    (bottom : B.Inside (33/20) (47/20))
    (high : B.Inside 2 (1543/500))
    (missing : ¬ B.Inside 2 (5/2)) :
    B.loU+B.side ≤ 2*B.c+(5/2)*B.s := by
  have uLower : B.loU < B.c*2+B.s*(5/2) := by
    linarith only [bottom.1,bc,canonical]
  have vLower : B.loV < -B.s*2+B.c*(5/2) := by
    linarith only [bottom.2.2.1,bc,bs]
  have vUpper : -B.s*2+B.c*(5/2) < B.loV+B.side := by
    linarith only [high.2.2.2,bc]
  apply le_of_not_gt
  intro uUpper
  exact missing ⟨uLower,by linarith only [uUpper],vLower,vUpper⟩

/-- Every canonical negative B, disjoint from A's forced point, contains
this point. No angular subdivision or pose enclosure is used. -/
theorem inward_point (B : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0) (canonical : -B.s ≤ B.c)
    (ha : 1 < B.side)
    (bottom : B.Inside (33/20) (47/20))
    (high : B.Inside 2 (1543/500))
    (missing : ¬ B.Inside 2 (5/2)) : B.Inside (7/5) (13/5) := by
  have cap := upper_face B bc bs canonical bottom high missing
  have span := (short_projections B (3/5) (-(1/10)) (by norm_num)).2.1
  exact ⟨by linarith only [cap,span,ha],
    by linarith only [bottom.2.1,bc,bs],
    by linarith only [bottom.2.2.1,canonical],
    by linarith only [high.2.2.2,bc,bs]⟩

/-- The genuine upper-right owner's auxiliary point leaves only two
explicit upper-face alternatives for B. -/
theorem right_faces (B : OpenSquare)
    (bc : 0 < B.c) (bs : B.s ≤ 0)
    (bottom : B.Inside (33/20) (47/20))
    (top : ClosedInside B (8/5) 3)
    (missing : ¬ B.Inside (113/50) 3) :
    B.loU+B.side ≤ (113/50)*B.c+3*B.s ∨
      B.loV+B.side ≤ -(113/50)*B.s+3*B.c := by
  have uLower : B.loU < B.c*(113/50)+B.s*3 := by
    linarith only [top.1,bc]
  have vLower : B.loV < -B.s*(113/50)+B.c*3 := by
    linarith only [bottom.2.2.1,bc,bs]
  by_cases uUpper : B.loU+B.side ≤ (113/50)*B.c+3*B.s
  · exact Or.inl uUpper
  · right
    apply le_of_not_gt
    intro vUpper
    exact missing ⟨uLower,by linarith only [uUpper],vLower,
      by linarith only [vUpper]⟩

#print axioms inward_point
end N12Compact.C849NegativePoints
