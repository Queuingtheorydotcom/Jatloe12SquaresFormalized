import Compact.Completion.OtherCases.C1090.NESelection

/-! Literal C1090 application: S=Q5, E=Q6, NW=Q7, SE corner=Q1,
bottom=Q9, right=Q10. The bottom interval belongs to one actual Q9.
This raw-owner application is separate from the missing finite entrance
which must supply its covering alternatives and original strict points.
No assertion that marker 1 is globally absent occurs here: in C1090 it
belongs to the distinct merged Q8 with mask 4098. -/
namespace N12Compact.Completion.OtherCases.C1090.NESelectionOwners
open S12 S12Pilot
set_option Elab.async false

structure Data (q : Fin 12 → OpenSquare) : Prop where
  side : ∀ i,1<(q i).side
  apart : ∀ i j,i≠j → ∀ x y,¬((q i).Inside x y ∧ (q j).Inside x y)
  southeastMarker : (q 5).Inside (47/20) (33/20)
  southeastF8 : (q 5).Inside 3 (87/50)
  southeastG8 : (q 5).Inside 3 (8/5)
  northeastMarker : (q 6).Inside (47/20) (47/20)
  northwestMarker : (q 7).Inside (33/20) (47/20)
  cornerPoint : (q 1).Inside 3 1
  cornerMarker : (q 1).Inside (1543/500) 1
  rightMarker : (q 10).Inside (1543/500) 2
  rightF9 : (q 10).Inside 3 (113/50)
  rightG9 : (q 10).Inside 3 (12/5)
  bottomG5 : (q 9).Inside (113/50) 1
  bottomAdvance : (q 9).Inside (14/5) 1
  fCover : (q 6).Inside 2 (113/50) ∨ (q 6).Inside (12/5) 3
  gCover : (q 6).Inside (113/50) 2 ∨ (q 6).Inside (113/50) 3

theorem bottom_bar (q : Fin 12 → OpenSquare) (h : Data q)
    (x : ℝ) (low : 113/50≤x) (high : x≤14/5) : (q 9).Inside x 1 := by
  let t := (50/27)*(x-113/50)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  convert inside_segment (q 9) (113/50) 1 (14/5) 1 t
    h.bottomG5 h.bottomAdvance tn tu using 1 <;> dsimp only [t] <;> ring

theorem input (q : Fin 12 → OpenSquare) (h : Data q) : NESelection.Input (q 5) (q 6) where
  sideS := h.side 5
  sideE := h.side 6
  apart := h.apart 5 6 (by decide)
  markerS := h.southeastMarker
  f8 := h.southeastF8
  g8 := h.southeastG8
  corner := fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.cornerPoint⟩
  cornerMarker := fun own => h.apart 5 1 (by decide) _ _ ⟨own,h.cornerMarker⟩
  rightMarker := fun own => h.apart 5 10 (by decide) _ _ ⟨own,h.rightMarker⟩
  bottom := fun x low high own => h.apart 5 9 (by decide) x 1 ⟨own,bottom_bar q h x low high⟩
  markerE := h.northeastMarker
  northwest := fun own => h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩
  f9 := fun own => h.apart 6 10 (by decide) _ _ ⟨own,h.rightF9⟩
  g9 := fun own => h.apart 6 10 (by decide) _ _ ⟨own,h.rightG9⟩
  fCover := h.fCover
  gCover := h.gCover

theorem selection (q : Fin 12 → OpenSquare) (h : Data q) :
    (q 6).Inside (113/50) 3 ∧ ((q 6).Inside (113/50) 2 → (q 6).Inside (12/5) 3) :=
  NESelection.selection (q 5) (q 6) (input q h)

#print axioms selection
end N12Compact.Completion.OtherCases.C1090.NESelectionOwners
