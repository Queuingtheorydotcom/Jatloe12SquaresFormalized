import Compact.Completion.OtherCases.MergedPending.WallReach
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! C700's actual paired southeast corner forces the right-wall origin.
The quarter-turn maps the corner's omitted upper halfpoint to the genuine
bottom8192 segment. Both corner walls and the entire same physical corner
are retained; no southwest or merged-square sign is assumed. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem c700_right_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 16384).Inside 3 2 := by
  let R := pullSwap (pullX (owner p 16384))
  let K := pullSwap (pullX (owner p 12))
  have boxR := container_pullSwap _ (container_pullX _ (box p 16384))
  have boxK := container_pullSwap _ (container_pullX _ (box p 12))
  have marker := seed _ p hf 16384 (by decide +kernel) (1543/500,2) (by decide +kernel)
  have cornerMarker := seed _ p hf 12 (by decide +kernel) (1543/500,1) (by decide +kernel)
  have corner := seed _ p hf 12 (by decide +kernel) (3,1) (by decide +kernel)
  norm_num at marker cornerMarker corner
  have sameRK : R.side=K.side :=
    (p.congruent _).trans (p.congruent _).symm
  have point := WallProfile.boundary_origin R K (457/500) (8/5)
    (side p 16384) sameRK
    (fun x y own => (boxR x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [R]; norm_num [inside_pullSwap,inside_pullX]; exact marker)
    (by
      dsimp only [R]
      norm_num [inside_pullSwap,inside_pullX]
      exact (c700_right_reach p hf).2 (8/5) (by norm_num) (by norm_num))
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullX]; exact corner)
    (by
      intro own
      have original : (owner p 12).Inside (5/2) 1 := by
        norm_num [K,inside_pullSwap,inside_pullX] at own
        exact own
      exact apart _ p hf 12 8192 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨original,(bottom_reach .c700 p hf).2 (5/2) (by norm_num) (by norm_num)⟩)
    (by
      intro x y both
      have first : (owner p 12).Inside (4-y) x := by
        simpa only [K,inside_pullSwap,inside_pullX] using both.1
      have last : (owner p 16384).Inside (4-y) x := by
        simpa only [R,inside_pullSwap,inside_pullX] using both.2
      exact apart _ p hf 12 16384 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨first,last⟩)
  dsimp only [R] at point
  norm_num [inside_pullSwap,inside_pullX] at point
  exact point

/-- The perpendicular transfer keeps the same actual paired corner.
Its omitted upper halfpoint is now strictly in actual right16384. -/
theorem c700_bottom_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 8192).Inside 2 1 := by
  let B := pullX (owner p 8192)
  let K := pullX (owner p 12)
  have boxB := container_pullX _ (box p 8192)
  have boxK := container_pullX _ (box p 12)
  have marker := seed _ p hf 8192 (by decide +kernel) (2,457/500) (by decide +kernel)
  have cornerMarker := seed _ p hf 12 (by decide +kernel) (3,457/500) (by decide +kernel)
  have corner := seed _ p hf 12 (by decide +kernel) (3,1) (by decide +kernel)
  norm_num at marker cornerMarker corner
  have sameBK : B.side=K.side :=
    (p.congruent _).trans (p.congruent _).symm
  have point := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 8192) sameBK
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num [inside_pullX]; exact marker)
    (by
      dsimp only [B]
      norm_num [inside_pullX]
      exact (bottom_reach .c700 p hf).2 (12/5) (by norm_num) (by norm_num))
    (by dsimp only [K]; norm_num [inside_pullX]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullX]; exact corner)
    (by
      intro own
      have original : (owner p 12).Inside 3 (3/2) := by
        norm_num [K,inside_pullX] at own
        exact own
      exact apart _ p hf 12 16384 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨original,(c700_right_reach p hf).2 (3/2) (by norm_num) (by norm_num)⟩)
    (by
      intro x y both
      have first : (owner p 12).Inside (4-x) y := by
        simpa only [K,inside_pullX] using both.1
      have last : (owner p 8192).Inside (4-x) y := by
        simpa only [B,inside_pullX] using both.2
      exact apart _ p hf 12 8192 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨first,last⟩)
  dsimp only [B] at point
  norm_num [inside_pullX] at point
  exact point

end
#print axioms c700_right_origin
#print axioms c700_bottom_origin
end N12Compact.MergedPending
