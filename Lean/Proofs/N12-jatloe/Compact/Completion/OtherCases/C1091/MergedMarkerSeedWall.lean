import Compact.Completion.OtherCases.C1091.MergedMarkerSeed
import Compact.Completion.C981.WallAdvance
import S12.Convex

/-! The actual-wall application of C1091-merged-marker-seed.md. The
merged square A supplies its newly proved seed; K supplies the omitted
corner, N supplies the omitted G3 and northwest marker, and L is the
actual contained left-wall square. No finite family entrance is assumed
proved here. This source translation has not been compiled. -/
namespace N12Compact.Completion.OtherCases.C1091.MergedMarkerSeed
open S12 S12Pilot
set_option Elab.async false

structure WallInput (A K N L : OpenSquare) : Prop where
  sideA : 1<A.side
  sideL : 1<L.side
  boxL : InsideContainer L
  mergedLeft : A.Inside (457/500) 1
  mergedCentral : A.Inside (33/20) (33/20)
  mergedLow : A.Inside 1 (87/50)
  corner : K.Inside 1 1
  northwestG3 : N.Inside (87/50) 2
  northwestMarker : N.Inside (33/20) (47/20)
  wallMarker : L.Inside (457/500) 2
  wallF1 : L.Inside 1 (113/50)
  wallG1 : L.Inside 1 (12/5)
  apartAK : ∀ x y,¬(A.Inside x y ∧ K.Inside x y)
  apartAN : ∀ x y,¬(A.Inside x y ∧ N.Inside x y)
  apartLA : ∀ x y,¬(L.Inside x y ∧ A.Inside x y)
  apartLN : ∀ x y,¬(L.Inside x y ∧ N.Inside x y)

theorem seed_of_owners (A K N L : OpenSquare) (h : WallInput A K N L) :
    A.Inside (19/25) (187/100) :=
  point_original A h.sideA h.mergedLeft h.mergedCentral
    (fun own => h.apartAK _ _ ⟨own,h.corner⟩)
    (fun own => h.apartAN _ _ ⟨own,h.northwestG3⟩)

/-- The old wall theorem receives the new merged-marker seed as an
actual foreign strict point, not as an extra omitted-point assumption. -/
theorem wall_advance (A K N L : OpenSquare) (h : WallInput A K N L) :
    L.Inside 1 (14/5) :=
  C981CompletionWallAdvance.point L h.sideL h.boxL h.wallMarker h.wallG1
    (fun own => h.apartLA _ _ ⟨own,h.mergedLow⟩)
    (fun own => h.apartLA _ _ ⟨own,seed_of_owners A K N L h⟩)
    (fun own => h.apartLN _ _ ⟨own,h.northwestMarker⟩)

/-- Both endpoints and every intervening point are strict in the same
actual L. In particular no segment joins points of different owners. -/
theorem wall_bar (A K N L : OpenSquare) (h : WallInput A K N L)
    (y : ℝ) (low : 113/50≤y) (high : y≤14/5) : L.Inside 1 y := by
  let t := (50/27)*(y-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment L 1 (113/50) 1 (14/5) t
    h.wallF1 (wall_advance A K N L h) tn tu using 1 <;>
    dsimp only [t] <;> ring

/-- Literal C1091 roles: merged A=Q4, corner K=Q0, northwest N=Q7,
left-wall L=Q8. Producing this raw input from the original case is a
separate entrance obligation; this theorem does not assert ExcludesCase. -/
theorem original_owner_bar (q : Fin 12 → OpenSquare)
    (h : WallInput (q 4) (q 0) (q 7) (q 8)) :
    (q 4).Inside (19/25) (187/100) ∧
      ∀ y : ℝ,113/50≤y → y≤14/5 → (q 8).Inside 1 y :=
  ⟨seed_of_owners _ _ _ _ h,wall_bar _ _ _ _ h⟩

#print axioms seed_of_owners
#print axioms wall_advance
#print axioms wall_bar
#print axioms original_owner_bar
end N12Compact.Completion.OtherCases.C1091.MergedMarkerSeed
