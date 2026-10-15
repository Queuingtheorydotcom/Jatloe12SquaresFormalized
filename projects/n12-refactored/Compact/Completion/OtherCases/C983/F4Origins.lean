import Compact.Completion.OtherCases.C983.F4Filters
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Geometry.WallUpperMissingReach

/-! Actual C983 wall origins and bars. The top origin comes from the
original paired northwest corner and the already certified left wall.
The right advance retains the inward auxiliary as an optional owned point. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

/-- This transfer needs the actual top F3, independently of the merged
branch. Every corner point and every wall is supplied by its real owner. -/
theorem top_origin_of_f3 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f3 : 3∈actual p 11) : (owners p 11).Inside 2 3 := by
  have marker : (owners p 11).Inside 2 (1543/500) := by
    have h := seed_inside p hf 11 (2,1543/500) (by decide +kernel)
    norm_num at h
    exact h
  have inner : (owners p 11).Inside (8/5) 3 := by
    have h := auxiliary_inside p 11 3 (by decide +kernel) f3
    simpa [auxPoints,fPoints,gPoints] using h
  have cornerMarker : (owners p 4).Inside 1 (1543/500) := by
    have h := seed_inside p hf 4 (1,1543/500) (by decide +kernel)
    norm_num at h
    exact h
  have cornerPoint : (owners p 4).Inside 1 3 := by
    have h := seed_inside p hf 4 (1,3) (by decide +kernel)
    norm_num at h
    exact h
  have foreign : (owners p 8).Inside 1 (5/2) :=
    left_bar p hf (5/2) (by norm_num) (by norm_num)
  have missing : ¬(owners p 4).Inside 1 (5/2) :=
    fun h => owners_apart p hf 4 8 (by decide +kernel) _ _ ⟨h,foreign⟩
  have boxB := container_pullY (owners p 11) (owners_contained p 11)
  have boxK := container_pullY (owners p 4) (owners_contained p 4)
  have origin := WallProfile.boundary_origin
    (pullY (owners p 11)) (pullY (owners p 4)) (457/500) (8/5)
    (owners_side p 11) (owners_same_side p 11 4)
    (fun x y h => (boxB x y h).2.2.1)
    (fun x y h => ⟨(boxK x y h).1,(boxK x y h).2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num only [inside_pullY]; exact marker)
    (by norm_num only [inside_pullY]; exact inner)
    (by norm_num only [inside_pullY]; exact cornerMarker)
    (by norm_num only [inside_pullY]; exact cornerPoint)
    (by norm_num only [inside_pullY]; exact missing)
    (by
      intro x y h
      simp only [inside_pullY] at h
      exact owners_apart p hf 4 11 (by decide +kernel) x (4-y) h)
  norm_num only [inside_pullY] at origin
  exact origin

theorem f4_top_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) : (owners p 11).Inside 2 3 :=
  top_origin_of_f3 p hf (f4_top p hf f4).1

/-- The actual right wall advances from its G9 whenever F8 is in the
different southeast square. Its own G6 membership is unrestricted. -/
theorem right_advance_of_f8 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f8 : 8∈actual p 5) (g9 : 19∈actual p 10) :
    (owners p 10).Inside 3 (64/25) := by
  have marker : (owners p 10).Inside (1543/500) 2 := by
    have h := seed_inside p hf 10 (1543/500,2) (by decide +kernel)
    norm_num at h
    exact h
  have upper : (owners p 10).Inside 3 (12/5) := by
    have h := auxiliary_inside p 10 19 (by decide +kernel) g9
    simpa [auxPoints,fPoints,gPoints] using h
  have southeast : (owners p 5).Inside 3 (87/50) := by
    have h := auxiliary_inside p 5 8 (by decide +kernel) f8
    simpa [auxPoints,fPoints,gPoints] using h
  have northeast : (owners p 6).Inside (47/20) (47/20) := by
    have h := seed_inside p hf 6 (47/20,47/20) (by decide +kernel)
    norm_num at h
    exact h
  have missingF : ¬(owners p 10).Inside 3 (87/50) :=
    fun h => owners_apart p hf 10 5 (by decide +kernel) _ _ ⟨h,southeast⟩
  have missingM : ¬(owners p 10).Inside (47/20) (47/20) :=
    fun h => owners_apart p hf 10 6 (by decide +kernel) _ _ ⟨h,northeast⟩
  have advance := WallUpperMissingReach.point (pullX (owners p 10))
    (owners_side p 10) (container_pullX _ (owners_contained p 10))
    (by norm_num only [inside_pullX]; exact marker)
    (by norm_num only [inside_pullX]; exact upper)
    (by norm_num only [inside_pullX]; exact missingF)
    (by norm_num only [inside_pullX]; exact missingM)
  norm_num only [inside_pullX] at advance
  exact advance

theorem right_bar_of_f8 (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f8 : 8∈actual p 5) (f9 : 9∈actual p 10) (g9 : 19∈actual p 10) :
    ∀ y : ℝ,113/50≤y → y≤64/25 → (owners p 10).Inside 3 y := by
  have low : (owners p 10).Inside 3 (113/50) := by
    have h := auxiliary_inside p 10 9 (by decide +kernel) f9
    simpa [auxPoints,fPoints,gPoints] using h
  intro y lower upper
  exact CommonCases.OriginalOwners.vertical_segment (owners p 10) 3 (113/50) (64/25) y
    low (right_advance_of_f8 p hf f8 g9) (by norm_num) lower upper

theorem f4_right_bar (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (f4 : 4∈actual p 7) :
    ∀ y : ℝ,113/50≤y → y≤64/25 → (owners p 10).Inside 3 y :=
  right_bar_of_f8 p hf (f4_southeast p hf f4)
    (f4_right p hf f4).1 (f4_right p hf f4).2

end
#print axioms f4_top_origin
#print axioms f4_right_bar
end N12Compact.Completion.OtherCases.C983

