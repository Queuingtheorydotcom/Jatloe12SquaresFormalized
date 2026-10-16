import Compact.Completion.FiniteCases.C975ResidualSelection
import Compact.Completion.OtherCases.C1090.ResidualCentralPoints
import Compact.Completion.OtherCases.F4PointTransfers
import Compact.Completion.OtherCases.SouthwestSupportPoint.Main
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Completion.C981.WallAdvance

/-! Literal central and wall producers after the C975 selection cuts.
The northeast mixed and top-only alternatives are retained separately.
Their northwest-marker and top-origin exclusions both use merged34816.
The southwest still owns its genuine F4. Source only, uncompiled. -/
namespace N12Compact.FiniteCases.C975Selection
open S12 S12Pilot C975Domains C975Entrance
open N12Compact.CommonCases.OriginalOwners
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem southeast_east (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 512).Inside (5/2) 2 :=
  F4PointTransfers.horizontal_original (owner p 512) (side p 512)
    (fixed p hf).southeastMarker (southeast_g6_point p hf) (fixed p hf).southeastF8
    (foreign p hf 512 256 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (fixed p hf).southwestF4)
    (foreign p hf 512 8192 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ ((bottom_reach p hf).2 _ (by norm_num) (by norm_num)))

/-- The mixed northeast's lower sharp point uses no distinct NW owner. -/
theorem northeast_mixed_sharp (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family)
    (mixed : (owner p 1024).Inside 2 (113/50)) :
    (owner p 1024).Inside (121/50) (54/25) := by
  have corner : (owner p 48).Inside 3 3 := by
    convert seed_point p hf 48 (by decide +kernel) (3,3) (by decide +kernel)
      using 1 <;> norm_num
  have point := C1090.ResidualCentralPoints.mixed_point ((owner p 1024).translated 2 2)
    (side p 1024)
    (by norm_num [inside_translated_iff]; exact (fixed p hf).northeastMarker)
    (by norm_num [inside_translated_iff]; exact mixed)
    (by norm_num [inside_translated_iff]; exact (northeast_selection p hf).1)
    (by norm_num [inside_translated_iff]; exact foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (fixed p hf).northwestMarker)
    (by norm_num [inside_translated_iff]; exact foreign p hf 1024 34816 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (top_origin p hf))
    (by norm_num [inside_translated_iff]; exact foreign p hf 1024 48 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ corner)
    (by norm_num [inside_translated_iff]; exact foreign p hf 1024 16384 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (fixed p hf).rightF9)
  norm_num [inside_translated_iff] at point
  exact point

/-- Each genuine NE alternative supplies its own sharp point. Both
transfer to the same actual southeast lower point, without a right origin. -/
theorem southeast_lower (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 512).Inside 3 (3/2) := by
  have transfer (a b : ℝ) (parameters : C1090.ResidualCentralPoints.Parameters a b)
      (point : (owner p 1024).Inside (2+a) (2+b)) :
      (owner p 512).Inside 3 (3/2) := by
    have result := C1090.ResidualCentralPoints.southeast_point
      ((owner p 512).translated 2 2) a b parameters (side p 512)
      (by norm_num [inside_translated_iff]; exact (fixed p hf).southeastMarker)
      (by norm_num [inside_translated_iff]; exact southeast_g6_point p hf)
      (by norm_num [inside_translated_iff]; exact (fixed p hf).southeastF8)
      (by norm_num [inside_translated_iff]; exact foreign p hf 512 256 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (southwest_south p hf))
      (fun own => apart _ p hf 512 1024 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _ ⟨(inside_translated_iff _ _ _ _ _).mp own,point⟩)
    norm_num [inside_translated_iff] at result
    exact result
  by_cases mixed : (owner p 1024).Inside 2 (113/50)
  · apply transfer (21/50) (4/25) (by constructor <;> norm_num)
    convert northeast_mixed_sharp p hf mixed using 1 <;> norm_num
  · apply transfer (21/40) (1/8) (by constructor <;> norm_num)
    convert northeast_upper_sharp p hf mixed using 1 <;> norm_num

/-- The genuine paired southeast corner transfers the bottom origin
after its outer halfpoint is supplied by the actual southeast512. -/
theorem bottom_origin (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 8192).Inside 2 1 := by
  have cornerMarker : (owner p 12).Inside 3 (457/500) := by
    convert seed_point p hf 12 (by decide +kernel) (3,457/500) (by decide +kernel)
      using 1 <;> norm_num
  have result := WallProfile.boundary_origin (pullX (owner p 8192)) (pullX (owner p 12))
    (457/500) (8/5) (side p 8192)
    ((p.congruent _).trans (p.congruent _).symm)
    (by
      intro x y own
      exact (box p 8192 _ _ ((inside_pullX _ _ _).mp own)).2.2.1)
    (by
      intro x y own
      have wall := box p 12 _ _ ((inside_pullX _ _ _).mp own)
      exact ⟨by linarith only [wall.2.1],wall.2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullX]; exact (fixed p hf).bottomMarker)
    (by norm_num [inside_pullX]; exact (fixed p hf).bottomF6)
    (by norm_num [inside_pullX]; exact cornerMarker)
    (by norm_num [inside_pullX]; exact (fixed p hf).southeastCorner)
    (by norm_num [inside_pullX]; exact foreign p hf 12 512 (by decide +kernel) (by decide +kernel) (by decide +kernel) _ _ (southeast_lower p hf))
    (by
      intro x y both
      exact apart _ p hf 12 8192 (by decide +kernel) (by decide +kernel)
        (by decide +kernel) _ _
        ⟨(inside_pullX _ _ _).mp both.1,(inside_pullX _ _ _).mp both.2⟩)
  norm_num [inside_pullX] at result
  exact result

/-- The actual left square advances past its G1 using the genuine
singleton2 off-row seed and the foreign merged-top marker. -/
theorem left_reach (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 4096).Inside 1 (14/5) := by
  have marker : (owner p 4096).Inside (457/500) 2 := by
    convert seed_point p hf 4096 (by decide +kernel) (457/500,2) (by decide +kernel)
      using 1 <;> norm_num
  have upper : (owner p 4096).Inside 1 (12/5) := by
    simpa [auxPoints,fPoints,gPoints] using aux_point p 4096 11 (by norm_num)
      (compulsory p hf).leftWall.2
  have off : (owner p 2).Inside (19/25) (187/100) := by
    convert seed_point p hf 2 (by decide +kernel) (19/25,187/100) (by decide +kernel)
      using 1 <;> norm_num
  exact C981CompletionWallAdvance.point (owner p 4096) (side p 4096) (box p 4096)
    marker upper
    (foreign p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (singleton_vertical p hf _ (by norm_num) le_rfl))
    (foreign p hf 4096 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ off)
    (foreign p hf 4096 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (fixed p hf).northwestMarker)

/-- The southwest support producer uses the actual F4 and both true
singletons. The northwest exclusion belongs to merged34816. -/
theorem southwest_support (p : NormalizedPacking) (hf : codedMarkerFamily p=family) :
    (owner p 256).Inside (127/100) (49/25) := by
  have h := fixed p hf
  exact SouthwestSupportPoint.point_of_neighbours (owner p 256) (owner p 1) (owner p 512)
    (side p 256) h.southwestMarker h.southwestF4 h.southwestG3
    (southwest_west p hf) (southwest_south p hf)
    (foreign p hf 256 34816 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ h.northwestMarker)
    (foreign p hf 256 8192 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (bottom_origin p hf))
    (foreign p hf 256 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (singleton_vertical p hf _ (by norm_num) (by norm_num)))
    (foreign p hf 256 2 (by decide +kernel) (by decide +kernel)
      (by decide +kernel) _ _ (singleton_vertical p hf _ (by norm_num) (by norm_num)))
    (singleton_horizontal p hf _ (by norm_num) (by norm_num))
    (singleton_horizontal p hf _ (by norm_num) le_rfl)
    h.southeastMarker (southeast_g6_point p hf)
    (apart _ p hf 256 1 (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (apart _ p hf 256 512 (by decide +kernel) (by decide +kernel) (by decide +kernel))

#print axioms southeast_lower
#print axioms bottom_origin
#print axioms left_reach
#print axioms southwest_support
end
end N12Compact.FiniteCases.C975Selection
