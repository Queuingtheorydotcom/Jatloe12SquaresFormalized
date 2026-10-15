import Compact.Completion.OtherCases.MergedPending.WallReach
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin

/-! The actual paired northwest corner supplies C700's left and top
boundary origins. The excluded corner halfpoint belongs to the other
ordinary wall owner. No central-marker or central-orientation premise is
used, and both full physical squares retain their real container walls. -/
namespace N12Compact.MergedPending
open S12 S12Pilot CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem c700_left_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 4096).Inside 1 2 := by
  let L := pullSwap (pullY (owner p 4096))
  let K := pullSwap (pullY (owner p 192))
  have boxL := container_pullSwap _ (container_pullY _ (box p 4096))
  have boxK := container_pullSwap _ (container_pullY _ (box p 192))
  have marker := seed _ p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
  have cornerMarker := seed _ p hf 192 (by decide +kernel) (457/500,3) (by decide +kernel)
  have corner := seed _ p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
  norm_num at marker cornerMarker corner
  have sameLK : L.side=K.side :=
    (p.congruent _).trans (p.congruent _).symm
  have point := WallProfile.boundary_origin L K (457/500) (8/5)
    (side p 4096) sameLK
    (fun x y own => (boxL x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [L]; norm_num [inside_pullSwap,inside_pullY]; exact marker)
    (by
      dsimp only [L]
      norm_num [inside_pullSwap,inside_pullY]
      exact (left_reach .c700 p hf).2 (12/5) (by norm_num) (by norm_num))
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullSwap,inside_pullY]; exact corner)
    (by
      intro own
      have original : (owner p 192).Inside (3/2) 3 := by
        norm_num [K,inside_pullSwap,inside_pullY] at own
        exact own
      exact apart _ p hf 192 32768 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨original,(top_reach .c700 p hf).2 (3/2) (by norm_num) (by norm_num)⟩)
    (by
      intro x y both
      have first : (owner p 192).Inside y (4-x) := by
        simpa only [K,inside_pullSwap,inside_pullY] using both.1
      have last : (owner p 4096).Inside y (4-x) := by
        simpa only [L,inside_pullSwap,inside_pullY] using both.2
      exact apart _ p hf 192 4096 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨first,last⟩)
  dsimp only [L] at point
  norm_num [inside_pullSwap,inside_pullY] at point
  exact point

theorem c700_top_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family .c700) : (owner p 32768).Inside 2 3 := by
  let T := pullY (owner p 32768)
  let K := pullY (owner p 192)
  have boxT := container_pullY _ (box p 32768)
  have boxK := container_pullY _ (box p 192)
  have marker := seed _ p hf 32768 (by decide +kernel) (2,1543/500) (by decide +kernel)
  have cornerMarker := seed _ p hf 192 (by decide +kernel) (1,1543/500) (by decide +kernel)
  have corner := seed _ p hf 192 (by decide +kernel) (1,3) (by decide +kernel)
  norm_num at marker cornerMarker corner
  have sameTK : T.side=K.side :=
    (p.congruent _).trans (p.congruent _).symm
  have point := WallProfile.boundary_origin T K (457/500) (8/5)
    (side p 32768) sameTK
    (fun x y own => (boxT x y own).2.2.1)
    (fun x y own => ⟨(boxK x y own).1,(boxK x y own).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by dsimp only [T]; norm_num [inside_pullY]; exact marker)
    (by
      dsimp only [T]
      norm_num [inside_pullY]
      exact (top_reach .c700 p hf).2 (8/5) (by norm_num) (by norm_num))
    (by dsimp only [K]; norm_num [inside_pullY]; exact cornerMarker)
    (by dsimp only [K]; norm_num [inside_pullY]; exact corner)
    (by
      intro own
      have original : (owner p 192).Inside 1 (5/2) := by
        norm_num [K,inside_pullY] at own
        exact own
      exact apart _ p hf 192 4096 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨original,(left_reach .c700 p hf).2 (5/2) (by norm_num) (by norm_num)⟩)
    (by
      intro x y both
      have first : (owner p 192).Inside x (4-y) := by
        simpa only [K,inside_pullY] using both.1
      have last : (owner p 32768).Inside x (4-y) := by
        simpa only [T,inside_pullY] using both.2
      exact apart _ p hf 192 32768 (by decide +kernel) (by decide +kernel) (by decide)
        _ _ ⟨first,last⟩)
  dsimp only [T] at point
  norm_num [inside_pullY] at point
  exact point

end
#print axioms c700_left_origin
#print axioms c700_top_origin
end N12Compact.MergedPending
