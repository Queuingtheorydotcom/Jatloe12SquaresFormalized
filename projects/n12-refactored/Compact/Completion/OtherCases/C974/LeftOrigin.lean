import Compact.Completion.OtherCases.C974.EarlyGeometry
import Compact.Completion.C981.WallAdvance

/-! The actual left-origin and top halfpoint argument of
C974-LEFT-ORIGIN-AND-MIDPOINT §§1–2. No segment at an absent marker
is used: marker11 appears only as a point exclusion. -/
namespace N12Compact.Completion.OtherCases.C974.OriginalData
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem left_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 (14/5) := by
  have h := fixed p hf
  exact C981CompletionWallAdvance.point _ (side p 8) (box p 8) h.leftMarker h.leftG1
    (foreign p hf 8 1 (by decide) _ _ (singleton_vertical p hf _ (by norm_num) le_rfl))
    (foreign p hf 8 1 (by decide) _ _ h.singleton1Seed) (missing_northwest p hf 8)

theorem top_left_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (36/25) 3 := by
  have point := WallUpperMissingReach.point (pullSwap (pullY (pullX (owners p 11))))
    (side p 11) (container_pullSwap _ (container_pullY _ (container_pullX _ (box p 11))))
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact (fixed p hf).topMarker)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact (top_pair p hf).1)
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]
        exact foreign p hf 11 7 (by decide) _ _ (northeast_g7 p hf))
    (by norm_num [inside_pullSwap,inside_pullY,inside_pullX]; exact missing_northwest p hf 11)
  norm_num [inside_pullSwap,inside_pullY,inside_pullX] at point
  exact point

theorem top_halfpoint (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 11).Inside (3/2) 3 :=
  CommonCases.OriginalOwners.horizontal_segment _ (36/25) (8/5) 3 (3/2)
    (top_left_reach p hf) (top_pair p hf).1 (by norm_num) (by norm_num) (by norm_num)

theorem left_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owners p 8).Inside 1 2 := by
  let B := pullSwap (pullY (owners p 8))
  let K := pullSwap (pullY (owners p 4))
  have boxB := container_pullSwap _ (container_pullY _ (box p 8))
  have boxK := container_pullSwap _ (container_pullY _ (box p 4))
  have cornerMarker : (owners p 4).Inside (457/500) 3 := by
    convert seed p hf 4 (457/500,3) (by decide +kernel) using 1 <;> norm_num
  have point := WallProfile.boundary_origin B K (457/500) (8/5)
    (side p 8) (same p 8 4)
    (fun x y own => (boxB x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY]; exact (fixed p hf).leftMarker)
    (by dsimp only [B]; norm_num [inside_pullSwap,inside_pullY]; exact (fixed p hf).leftG1)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact (fixed p hf).northwestCorner)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]
        exact foreign p hf 4 11 (by decide) _ _ (top_halfpoint p hf))
    (by
      intro x y both
      have first : (owners p 4).Inside y (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY] using both.1
      have last : (owners p 8).Inside y (4-x) := by
        simpa only [B,inside_pullSwap,inside_pullY] using both.2
      exact apart p hf 4 8 (by decide) _ _ ⟨first,last⟩)
  dsimp only [B] at point
  norm_num [inside_pullSwap,inside_pullY] at point
  exact point

end
#print axioms left_origin
end N12Compact.Completion.OtherCases.C974.OriginalData
