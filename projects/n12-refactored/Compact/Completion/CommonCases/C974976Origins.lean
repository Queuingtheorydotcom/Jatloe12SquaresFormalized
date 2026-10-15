import Compact.Completion.CommonCases.C974976Central
import Compact.Completion.CommonCases.OriginalOwners
import Compact.Geometry.WallLowerReach
import Compact.Completion.OtherCases.WallProfile.BoundaryOrigin
import Compact.Completion.OtherCases.C1090.ResidualCentralPoints

/-! The original C974/C976 top-origin and southeast-lower/bottom-origin
transfers. The weaker left-wall theorem omits the inward G3 point, not
the northwest marker; it therefore applies to the merged C976 owner.
Each foreign point stays in its explicit physical square. -/
namespace N12Compact.CommonCases.C974976Central
open S12 S12Pilot
open N12Compact.Completion.OtherCases
set_option Elab.async false
noncomputable section

theorem top_origin (L T K : OpenSquare)
    (sideL : 1<L.side) (sideT : 1<T.side) (same : T.side=K.side)
    (boxL : InsideContainer L) (boxT : InsideContainer T) (boxK : InsideContainer K)
    (leftMarker : L.Inside (457/500) 2) (leftG1 : L.Inside 1 (12/5))
    (missingF0 : ¬L.Inside 1 (87/50)) (missingG3 : ¬L.Inside (87/50) 2)
    (topMarker : T.Inside 2 (1543/500)) (topF3 : T.Inside (8/5) 3)
    (cornerMarker : K.Inside 1 (1543/500)) (corner : K.Inside 1 3)
    (apartKL : ∀ x y,¬(K.Inside x y ∧ L.Inside x y))
    (apartKT : ∀ x y,¬(K.Inside x y ∧ T.Inside x y)) : T.Inside 2 3 := by
  have reach := WallLowerReach.point L sideL boxL leftMarker leftG1 missingF0 missingG3
  have half : L.Inside 1 (5/2) := OriginalOwners.vertical_segment L 1 (12/5) (64/25)
    (5/2) leftG1 reach (by norm_num) (by norm_num) (by norm_num)
  have result := WallProfile.boundary_origin (pullY T) (pullY K)
    (457/500) (8/5) sideT same
    (by
      intro x y own
      have wall := boxT _ _ ((inside_pullY _ _ _).mp own)
      linarith only [wall.2.2.2])
    (by
      intro x y own
      have wall := boxK _ _ ((inside_pullY _ _ _).mp own)
      exact ⟨wall.1,by linarith only [wall.2.2.2]⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullY]; exact topMarker)
    (by norm_num [inside_pullY]; exact topF3)
    (by norm_num [inside_pullY]; exact cornerMarker)
    (by norm_num [inside_pullY]; exact corner)
    (by
      intro own
      apply apartKL _ _ ⟨?_,half⟩
      convert (inside_pullY _ _ _).mp own using 1 <;> norm_num)
    (by
      intro x y pair
      exact apartKT _ _ ⟨(inside_pullY _ _ _).mp pair.1,(inside_pullY _ _ _).mp pair.2⟩)
  norm_num [inside_pullY] at result
  exact result

/-- The two exact northeast alternatives supply their own strict point
to the same southeast square. Neither a right origin nor a surrogate
corner is used. -/
theorem southeast_lower (S N : OpenSquare) (h : EndingInput S N)
    (g6 : S.Inside (113/50) 2) : S.Inside 3 (3/2) := by
  have transfer (a b : ℝ) (parameters : C1090.ResidualCentralPoints.Parameters a b)
      (foreign : N.Inside (2+a) (2+b)) : S.Inside 3 (3/2) := by
    have point := C1090.ResidualCentralPoints.southeast_point (S.translated 2 2)
      a b parameters h.sideS
      (by norm_num [inside_translated_iff]; exact h.markerS)
      (by norm_num [inside_translated_iff]; exact g6)
      (by norm_num [inside_translated_iff]; exact h.f8)
      (by norm_num [inside_translated_iff]; exact h.southwest)
      (fun own => h.apart _ _ ⟨(inside_translated_iff _ _ _ _ _).mp own,foreign⟩)
    norm_num [inside_translated_iff] at point
    exact point
  by_cases mixed : N.Inside 2 (113/50)
  · have point := C1090.ResidualCentralPoints.mixed_point (N.translated 2 2) h.sideE
      (by norm_num [inside_translated_iff]; exact h.markerE)
      (by norm_num [inside_translated_iff]; exact mixed)
      (by norm_num [inside_translated_iff]; exact northeast_g7 S N h.toInput)
      (by norm_num [inside_translated_iff]; exact h.northwest)
      (by norm_num [inside_translated_iff]; exact h.topOrigin)
      (by norm_num [inside_translated_iff]; exact h.northeastCorner)
      (by norm_num [inside_translated_iff]; exact h.f9)
    norm_num [inside_translated_iff] at point
    apply transfer (21/50) (4/25) (by constructor <;> norm_num)
    convert point using 1 <;> norm_num
  · have point := UpperBarPoint.point_original N h.sideE h.markerE
      (northeast_f7 S N h.toInput) mixed h.topOrigin h.northeastCorner h.rightBar
    apply transfer (21/40) (1/8) (by constructor <;> norm_num)
    convert point using 1 <;> norm_num

theorem bottom_origin (B K S : OpenSquare)
    (sideB : 1<B.side) (same : B.side=K.side)
    (boxB : InsideContainer B) (boxK : InsideContainer K)
    (bottomMarker : B.Inside 2 (457/500)) (bottomF6 : B.Inside (12/5) 1)
    (cornerMarker : K.Inside 3 (457/500)) (corner : K.Inside 3 1)
    (southLower : S.Inside 3 (3/2))
    (apartKS : ∀ x y,¬(K.Inside x y ∧ S.Inside x y))
    (apartKB : ∀ x y,¬(K.Inside x y ∧ B.Inside x y)) : B.Inside 2 1 := by
  have result := WallProfile.boundary_origin (pullX B) (pullX K)
    (457/500) (8/5) sideB same
    (by intro x y own; exact (boxB _ _ ((inside_pullX _ _ _).mp own)).2.2.1)
    (by
      intro x y own
      have wall := boxK _ _ ((inside_pullX _ _ _).mp own)
      exact ⟨by linarith only [wall.2.1],wall.2.2.1⟩)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [inside_pullX]; exact bottomMarker)
    (by norm_num [inside_pullX]; exact bottomF6)
    (by norm_num [inside_pullX]; exact cornerMarker)
    (by norm_num [inside_pullX]; exact corner)
    (by
      intro own
      apply apartKS _ _ ⟨?_,southLower⟩
      convert (inside_pullX _ _ _).mp own using 1 <;> norm_num)
    (by
      intro x y pair
      exact apartKB _ _ ⟨(inside_pullX _ _ _).mp pair.1,(inside_pullX _ _ _).mp pair.2⟩)
  norm_num [inside_pullX] at result
  exact result

end
#print axioms top_origin
#print axioms southeast_lower
#print axioms bottom_origin
end N12Compact.CommonCases.C974976Central
