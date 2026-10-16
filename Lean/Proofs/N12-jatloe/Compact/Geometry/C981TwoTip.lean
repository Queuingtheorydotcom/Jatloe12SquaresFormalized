import S12.ShortCluster

/-! The all-orientation two-tip obstruction.  The two point-completion steps
are proved directly from the square's four bands.  In particular, neither
step requires a strict angle condition: the four zero dot products in the
geometric argument are retained exactly.  No container or upper side bound
is used, and excluded points may lie on the boundary. -/
namespace N12Compact.C981TwoTip

open S12 S12Pilot
set_option Elab.async false

/-- The first chord and its missing tip force the rational point X. -/
theorem first_tip (A : OpenSquare) (side : 1 < A.side)
    (marker : A.Inside (47/20) (47/20))
    (top : A.Inside (12/5) 3)
    (missing : ¬ A.Inside (87/50) 3) :
    A.Inside (12/5) (779/325) := by
  obtain ⟨m0,m1,m2,m3⟩ := marker
  obtain ⟨t0,t1,t2,t3⟩ := top
  obtain ⟨d0,d1,d2,d3⟩ := short_projections A
    (12/5-87/50) (779/325-3) (by norm_num)
  by_contra absent
  simp only [OpenSquare.Inside,InBands,not_and_or,not_lt] at missing absent
  rcases missing with h | h | h | h <;>
    rcases absent with k | k | k | k <;>
    linarith only [side,m0,m1,m2,m3,t0,t1,t2,t3,d0,d1,d2,d3,h,k]

/-- The second chord and its missing tip force the rational point Y. -/
theorem second_tip (B : OpenSquare) (side : 1 < B.side)
    (central : B.Inside (113/50) 2)
    (right : B.Inside 3 (12/5))
    (missing : ¬ B.Inside 3 (87/50)) :
    B.Inside (4441/1850) (12/5) := by
  obtain ⟨c0,c1,c2,c3⟩ := central
  obtain ⟨r0,r1,r2,r3⟩ := right
  obtain ⟨d0,d1,d2,d3⟩ := short_projections B
    (4441/1850-3) (12/5-87/50) (by norm_num)
  by_contra absent
  simp only [OpenSquare.Inside,InBands,not_and_or,not_lt] at missing absent
  rcases missing with h | h | h | h <;>
    rcases absent with k | k | k | k <;>
    linarith only [side,c0,c1,c2,c3,r0,r1,r2,r3,d0,d1,d2,d3,h,k]

/-- X is a strict convex combination of the two second-owner chord points
and Y, with weights 1/130, 1/1109 and 142931/144170. -/
theorem common_tip (B : OpenSquare)
    (central : B.Inside (113/50) 2)
    (right : B.Inside 3 (12/5))
    (tip : B.Inside (4441/1850) (12/5)) :
    B.Inside (12/5) (779/325) := by
  obtain ⟨c0,c1,c2,c3⟩ := central
  obtain ⟨r0,r1,r2,r3⟩ := right
  obtain ⟨t0,t1,t2,t3⟩ := tip
  dsimp [OpenSquare.Inside,InBands]
  exact ⟨by linarith only [c0,r0,t0], by linarith only [c1,r1,t1],
    by linarith only [c2,r2,t2], by linarith only [c3,r3,t3]⟩

/-- Complete contradiction for two actual, disjoint square interiors. -/
theorem impossible (A B : OpenSquare) (aSide : 1 < A.side) (bSide : 1 < B.side)
    (marker : A.Inside (47/20) (47/20)) (top : A.Inside (12/5) 3)
    (aMissing : ¬ A.Inside (87/50) 3)
    (central : B.Inside (113/50) 2) (right : B.Inside 3 (12/5))
    (bMissing : ¬ B.Inside 3 (87/50))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)) : False :=
  apart (12/5) (779/325)
    ⟨first_tip A aSide marker top aMissing,
      common_tip B central right (second_tip B bSide central right bMissing)⟩

end N12Compact.C981TwoTip
