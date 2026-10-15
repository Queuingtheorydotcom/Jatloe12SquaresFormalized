import S12.Seeds

/-! The C1090 merged-left seed is an existing wall-bridge consequence
of the actual markers 1 and 12 in one square (mask 4098). This wrapper
does not invoke the absent MERGED-LEFT-SEED.md, does not assert its extra
center bounds, and never treats marker 1 as globally unowned. -/
namespace N12Compact.Completion.OtherCases.C1090.MergedLeftSeed
open S12 S12Pilot
set_option Elab.async false

theorem segment (L : OpenSquare) (side : 1<L.side)
    (wall : ∀ x y,L.Inside x y → 0≤x)
    (marker1 : L.Inside (457/500) 1) (marker12 : L.Inside (457/500) 2) :
    ∀ y : ℝ,5/4≤y → y≤7/4 → L.Inside 1 y :=
  fun y low high => wall_bridge_forces L side wall marker1 marker12 y low high

theorem of_exact_markers (L : OpenSquare) (side : 1<L.side)
    (box : InsideContainer L) (markers : ExactMarkers L ({1,12} : Finset Marker)) :
    ∀ y : ℝ,5/4≤y → y≤7/4 → L.Inside 1 y := by
  have first : Owns L 1 := (markers 1).mpr (by decide)
  have second : Owns L 12 := (markers 12).mpr (by decide)
  exact segment L side (fun x y own => (box x y own).1)
    (by simpa [Owns,marker] using first)
    (by simpa [Owns,marker] using second)

/-- Marker 1 is strict in actual Q8 and therefore omitted by Q0.
Only this owner-specific omission may be used in the singleton theorem. -/
theorem marker1_foreign_to_singleton (q : Fin 12 → OpenSquare)
    (marker1 : (q 8).Inside (457/500) 1)
    (apart : ∀ x y,¬((q 0).Inside x y ∧ (q 8).Inside x y)) :
    ¬(q 0).Inside (457/500) 1 := fun own => apart _ _ ⟨own,marker1⟩

theorem actual_segment (q : Fin 12 → OpenSquare) (side : 1<(q 8).side)
    (box : InsideContainer (q 8))
    (marker1 : (q 8).Inside (457/500) 1) (marker12 : (q 8).Inside (457/500) 2) :
    ∀ y : ℝ,5/4≤y → y≤7/4 → (q 8).Inside 1 y :=
  segment (q 8) side (fun x y own => (box x y own).1) marker1 marker12

#print axioms of_exact_markers
#print axioms actual_segment
end N12Compact.Completion.OtherCases.C1090.MergedLeftSeed
