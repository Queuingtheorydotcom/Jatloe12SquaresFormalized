import Compact.Geometry.MergedLeftCornerSector

/-! A center escape by the merged left central owner consumes a real
auxiliary point. The three excluded points are retained explicitly: in
the original applications they belong to the two lower corner owners
and the left wall. No auxiliary budget is assumed in this geometry. -/
namespace N12Compact.MergedLeftEscapeAux
open S12 S12Pilot
set_option Elab.async false

private theorem transverse_margin (A : OpenSquare)
    (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (slope : 2331*A.s < 1300*A.c) :
    (13/25)*A.c+A.s ≤ 1 := by
  have cone : 5*A.s ≤ 3*A.c := by linarith only [slope,hc]
  have product := mul_nonneg hc.le (sub_nonneg.mpr cone)
  have square : ((13/25)*A.c+A.s)^2 ≤ 1 := by
    nlinarith only [A.unit_normal,product,sq_nonneg A.c]
  nlinarith only [square,sq_nonneg ((13/25)*A.c+A.s-1)]

/-- In the canonical positive sector, the escape necessarily owns F4.
Together with the original one-point exempt budget, this restores the
exact-one F domains for every non-exempt owner. -/
theorem inward (A : OpenSquare) (side : 1 < A.side)
    (hc : 0 < A.c) (hs : 0 ≤ A.s) (order : A.s ≤ A.c)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (center : ¬ A.Inside 2 2)
    (leftLow : ¬ A.Inside 1 (87/50))
    (leftHigh : ¬ A.Inside 1 (113/50))
    (corner : ¬ A.Inside (8/5) 1) :
    A.Inside 2 (87/50) := by
  have cap := MergedLeftEscape.center_cap A hc hs order bottom top center
  have low := MergedLeftCornerSector.lower_u A side hc hs order
    bottom top center leftLow corner
  have sector := MergedLeftCornerSector.sector A side hc hs order
    bottom top center leftLow corner
  have upper := MergedLeftEscape.upper_v A side hc hs bottom top cap leftHigh
  have margin := transverse_margin A hc hs sector.2.2
  have cu : A.c ≤ 1 := by
    nlinarith only [A.unit_normal,sq_nonneg A.s,hc]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [bottom.1,hc,hs]
  · linarith only [low,side,cu]
  · linarith only [upper,side,margin]
  · linarith only [top.2.2.2,hc,hs]

/-- Both angle signs are included. The upper sign uses the genuine top
point (1.6,3), obtained from the top wall in the original domains. -/
theorem inward_or (A : OpenSquare) (side : 1 < A.side)
    (bottom : A.Inside (33/20) (33/20))
    (top : A.Inside (33/20) (47/20))
    (center : ¬ A.Inside 2 2)
    (leftLow : ¬ A.Inside 1 (87/50))
    (leftHigh : ¬ A.Inside 1 (113/50))
    (cornerLow : ¬ A.Inside (8/5) 1)
    (cornerHigh : ¬ A.Inside (8/5) 3) :
    A.Inside 2 (87/50) ∨ A.Inside 2 (113/50) := by
  obtain ⟨B,hc,order,same,inside,_⟩ := ClosedFrames.canonical_frame A
  have sideB : 1 < B.side := by simpa only [same] using side
  have bottomB := (inside _ _).mpr bottom
  have topB := (inside _ _).mpr top
  have centerB : ¬ B.Inside 2 2 := fun h => center ((inside _ _).mp h)
  have lowB : ¬ B.Inside 1 (87/50) := fun h => leftLow ((inside _ _).mp h)
  have highB : ¬ B.Inside 1 (113/50) := fun h => leftHigh ((inside _ _).mp h)
  by_cases positive : 0 ≤ B.s
  · exact Or.inl ((inside _ _).mp (inward B sideB hc positive
      (by simpa only [abs_of_nonneg positive] using order)
      bottomB topB centerB lowB highB
      (fun h => cornerLow ((inside _ _).mp h))))
  · have negative : B.s ≤ 0 := (lt_of_not_ge positive).le
    have reflected := inward (pullY B) sideB hc
      (by dsimp [pullY]; linarith only [negative])
      (by simpa only [pullY,abs_of_nonpos negative] using order)
      ((inside_pullY B _ _).mpr (by convert topB using 1 <;> norm_num))
      ((inside_pullY B _ _).mpr (by convert bottomB using 1 <;> norm_num))
      (fun h => centerB (by convert (inside_pullY B _ _).mp h using 1 <;> norm_num))
      (fun h => highB (by convert (inside_pullY B _ _).mp h using 1 <;> norm_num))
      (fun h => lowB (by convert (inside_pullY B _ _).mp h using 1 <;> norm_num))
      (fun h => cornerHigh ((inside _ _).mp
        (by convert (inside_pullY B _ _).mp h using 1 <;> norm_num)))
    exact Or.inr ((inside _ _).mp
      (by convert (inside_pullY B _ _).mp reflected using 1 <;> norm_num))

#print axioms inward
#print axioms inward_or
end N12Compact.MergedLeftEscapeAux
