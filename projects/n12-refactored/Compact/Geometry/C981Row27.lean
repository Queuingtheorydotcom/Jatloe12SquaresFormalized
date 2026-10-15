import Compact.Geometry.WallLowerReach
import S12.ShortCluster

/-! The original row-27 obstruction. The two point completions keep every
excluding face, including equality at the foreign boundary. The wall square,
central square and top square are the same physical owners throughout. -/
namespace N12Compact.C981Row27Geometry

open S12 S12Pilot
set_option Elab.async false

theorem first_point (C : OpenSquare) (side : 1 < C.side)
    (marker : C.Inside (33/20) (47/20))
    (inward : C.Inside (87/50) 2)
    (foreign : ¬ C.Inside (457/500) 2) :
    C.Inside (87/50) (54/25) := by
  obtain ⟨m0,m1,m2,m3⟩ := marker
  obtain ⟨d0,d1,d2,d3⟩ := inward
  obtain ⟨s0,s1,s2,s3⟩ := short_projections C
    (87/50-457/500) (54/25-2) (by norm_num)
  by_contra absent
  simp only [OpenSquare.Inside,InBands,not_and_or,not_lt] at foreign absent
  rcases foreign with h | h | h | h <;>
    rcases absent with k | k | k | k <;>
    linarith only [side,m0,m1,m2,m3,d0,d1,d2,d3,s0,s1,s2,s3,h,k]

theorem second_point (C : OpenSquare) (side : 1 < C.side)
    (inward : C.Inside (87/50) (54/25))
    (top : C.Inside (8/5) 3)
    (foreign : ¬ C.Inside 1 (64/25)) :
    C.Inside (48/25) (64/25) := by
  obtain ⟨p0,p1,p2,p3⟩ := inward
  obtain ⟨b0,b1,b2,b3⟩ := top
  obtain ⟨s0,s1,s2,s3⟩ := short_projections C (23/25) 0 (by norm_num)
  by_contra absent
  simp only [OpenSquare.Inside,InBands,not_and_or,not_lt] at foreign absent
  rcases foreign with h | h | h | h <;>
    rcases absent with k | k | k | k <;>
    linarith only [side,p0,p1,p2,p3,b0,b1,b2,b3,s0,s1,s2,s3,h,k]

theorem top_point (T : OpenSquare)
    (inward : T.Inside 2 (113/50))
    (left : T.Inside (87/50) 3)
    (right : T.Inside (12/5) 3) :
    T.Inside (48/25) (64/25) := by
  obtain ⟨a0,a1,a2,a3⟩ := inward
  obtain ⟨e0,e1,e2,e3⟩ := left
  obtain ⟨f0,f1,f2,f3⟩ := right
  dsimp [OpenSquare.Inside,InBands]
  exact ⟨by linarith only [a0,e0,f0], by linarith only [a1,e1,f1],
    by linarith only [a2,e2,f2], by linarith only [a3,e3,f3]⟩

theorem impossible (C L T : OpenSquare)
    (cSide : 1 < C.side) (lSide : 1 < L.side)
    (box : InsideContainer L)
    (marker : C.Inside (33/20) (47/20))
    (central : C.Inside (87/50) 2) (top : C.Inside (8/5) 3)
    (wall : L.Inside (457/500) 2) (wallUpper : L.Inside 1 (12/5))
    (wallMissing : ¬ L.Inside 1 (87/50))
    (inward : T.Inside 2 (113/50))
    (left : T.Inside (87/50) 3) (right : T.Inside (12/5) 3)
    (cApartL : ∀ x y, ¬ (C.Inside x y ∧ L.Inside x y))
    (cApartT : ∀ x y, ¬ (C.Inside x y ∧ T.Inside x y)) : False := by
  have reach := WallLowerReach.point L lSide box wall wallUpper wallMissing
    (fun h => cApartL (87/50) 2 ⟨central,h⟩)
  have first := first_point C cSide marker central
    (fun h => cApartL (457/500) 2 ⟨h,wall⟩)
  have second := second_point C cSide first top
    (fun h => cApartL 1 (64/25) ⟨h,reach⟩)
  exact cApartT (48/25) (64/25) ⟨second,top_point T inward left right⟩

#print axioms impossible
end N12Compact.C981Row27Geometry
