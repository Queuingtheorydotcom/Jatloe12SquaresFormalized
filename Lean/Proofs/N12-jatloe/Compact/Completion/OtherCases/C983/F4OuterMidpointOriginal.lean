import Compact.Completion.OtherCases.C983.F4CentralFinal
import Compact.Completion.OtherCases.C983.F4OuterMidpoint
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! Original-owner adapter for the completed outer-midpoint support
argument. The all-angle southeast-frame theorem and merged-center theorem
remain explicit prerequisites of this adapter. In particular no point is
assigned an owner merely because another square omits it. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem f4_outer_midpoint_of_frame (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) (noF5 : 5∉actual p 7)
    (center : (owners p 7).Inside 2 2)
    (E : OpenSquare) (t : ℝ) (shape : E.side=(owners p 5).side)
    (physical : ∀ x y,E.Inside x y ↔ (owners p 5).Inside (x+2) (y+2))
    (data : F4BottomMidpoint.SoutheastData E t)
    (half : t/(1+E.c)<3/20) (lowerU : (13/50)*t≤E.loU) :
    (owners p 5).Inside 3 (3/2) := by
  let W := (owners p 7).translated 2 2
  have south : (owners p 7).Inside (33/20) (33/20) := by
    have h := seed_inside p hf 7 (33/20,33/20) (by decide +kernel)
    norm_num at h
    exact h
  have north : (owners p 7).Inside (33/20) (47/20) := by
    have h := seed_inside p hf 7 (33/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have inward : (owners p 7).Inside 2 (87/50) := by
    have h := auxiliary_inside p 7 4 (by decide +kernel) f4
    simpa [auxPoints,fPoints,gPoints] using h
  have absent : ¬(owners p 7).Inside 2 (113/50) := by
    intro own
    apply noF5
    exact (point_exact p 7 5 (by decide +kernel)).mp
      (by simpa [auxPoints,fPoints,gPoints] using own)
  have corner : (owners p 1).Inside 1 (8/5) := by
    have labels : ∀ owned∈originalComponents 1,10∈owned := by decide +kernel
    have h := auxiliary_inside p 1 10 (by decide +kernel)
      (labels _ (original_actual_mem p hf 1))
    simpa [auxPoints,fPoints,gPoints] using h
  have east : E.Inside (1/2) 0 := by
    apply (physical _ _).mpr
    norm_num
    exact f4_southeast_crosspoint p hf f4
  have input : F4OuterMidpoint.Input W E t :=
    { southeast := data
      same := (owners_same_side p 7 5).trans shape.symm
      half := half
      lowerU := lowerU
      east := east
      southwest := by dsimp only [W]; norm_num only [inside_translated_iff]; exact south
      northwest := by dsimp only [W]; norm_num only [inside_translated_iff]; exact north
      inward := by dsimp only [W]; norm_num only [inside_translated_iff]; exact inward
      center := by dsimp only [W]; norm_num only [inside_translated_iff]; exact center
      missingNorth := by
        dsimp only [W]
        norm_num only [inside_translated_iff]
        exact absent
      missingLeft := by
        dsimp only [W]
        norm_num only [inside_translated_iff]
        exact fun own => owners_apart p hf 7 8 (by decide +kernel) _ _
          ⟨own,(left_aux p hf).1⟩
      missingCorner := by
        dsimp only [W]
        norm_num only [inside_translated_iff]
        exact fun own => owners_apart p hf 7 1 (by decide +kernel) _ _ ⟨own,corner⟩
      apart := by
        intro x y own
        exact owners_apart p hf 7 5 (by decide +kernel) (x+2) (y+2)
          ⟨by simpa only [add_comm] using (inside_translated_iff (owners p 7) 2 2 x y).mp own.1,(physical x y).mp own.2⟩ }
  have point := (physical _ _).mp (F4OuterMidpoint.inside W E t input)
  norm_num at point
  exact point

/-- Section 5's original paired southeast corner and bottom-wall transfer.
The corner and bottom square remain Q2 and Q9 under the horizontal reflection. -/
theorem bottom_origin_of_southeast_outer (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (outer : (owners p 5).Inside 3 (3/2)) :
    (owners p 9).Inside 2 1 := by
  let B := pullX (owners p 9)
  let K := pullX (owners p 2)
  have boxB := container_pullX _ (owners_contained p 9)
  have boxK := container_pullX _ (owners_contained p 2)
  have marker : (owners p 9).Inside 2 (457/500) := by
    have h := seed_inside p hf 9 (2,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have cornerMarker : (owners p 2).Inside 3 (457/500) := by
    have h := seed_inside p hf 2 (3,457/500) (by decide +kernel)
    norm_num at h
    exact h
  have cornerPoint : (owners p 2).Inside 3 1 := by
    have h := seed_inside p hf 2 (3,1) (by decide +kernel)
    norm_num at h
    exact h
  have missing : ¬(owners p 2).Inside 3 (3/2) :=
    fun own => owners_apart p hf 2 5 (by decide +kernel) _ _ ⟨own,outer⟩
  have origin := WallProfile.boundary_origin B K (457/500) (8/5)
    (owners_side p 9) (owners_same_side p 9 2)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num only [inside_pullX]; exact marker)
    (by dsimp only [B]; norm_num only [inside_pullX]; exact (bottom_aux p hf).1)
    (by dsimp only [K]; norm_num only [inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num only [inside_pullX]; exact cornerPoint)
    (by dsimp only [K]; norm_num only [inside_pullX]; exact missing)
    (by
      intro x y own
      have hK : (owners p 2).Inside (4-x) y := by
        simpa only [K,inside_pullX] using own.1
      have hB : (owners p 9).Inside (4-x) y := by
        simpa only [B,inside_pullX] using own.2
      exact owners_apart p hf 2 9 (by decide +kernel) _ _ ⟨hK,hB⟩)
  dsimp only [B] at origin
  norm_num only [inside_pullX] at origin
  exact origin

end
#print axioms f4_outer_midpoint_of_frame
#print axioms bottom_origin_of_southeast_outer
end N12Compact.Completion.OtherCases.C983
