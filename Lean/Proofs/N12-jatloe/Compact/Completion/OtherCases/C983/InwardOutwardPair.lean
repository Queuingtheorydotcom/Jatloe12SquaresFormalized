import Compact.Completion.CommonCases.InwardPoint
import Compact.Completion.CommonCases.OutwardPoint

/-! The genuine inward/outward duplicate in the C983 central reduction.
Every foreign exclusion comes from one displayed actual owner, except the
explicit omitted northeast auxiliary. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false

theorem inward_outward_impossible (N E B C R W : OpenSquare)
    (side : 1 < N.side) (same : N.side=E.side)
    (nMarker : N.Inside (47/20) (47/20))
    (nInward : N.Inside 2 (113/50)) (nElbow : N.Inside (113/50) 2)
    (nMissingTop : ¬N.Inside (12/5) 3)
    (eMarker : E.Inside (47/20) (33/20))
    (eOutward : E.Inside 3 (87/50)) (eUpper : E.Inside 3 (8/5))
    (wMarker : W.Inside (33/20) (47/20))
    (rMarker : R.Inside (1543/500) 2)
    (cCorner : C.Inside 3 1) (cMarker : C.Inside (1543/500) 1)
    (bottomBar : ∀ z : ℝ, 113/50 ≤ z → z ≤ 14/5 → B.Inside z 1)
    (apartNE : ∀ x y, ¬(N.Inside x y ∧ E.Inside x y))
    (apartNW : ∀ x y, ¬(N.Inside x y ∧ W.Inside x y))
    (apartER : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y))
    (apartEC : ∀ x y, ¬(E.Inside x y ∧ C.Inside x y))
    (apartEB : ∀ x y, ¬(E.Inside x y ∧ B.Inside x y)) : False := by
  have nMissingSE : ¬N.Inside (47/20) (33/20) :=
    fun h => apartNE _ _ ⟨h,eMarker⟩
  have nMissingNW : ¬N.Inside (33/20) (47/20) :=
    fun h => apartNW _ _ ⟨h,wMarker⟩
  have eMissingG : ¬E.Inside (113/50) 2 :=
    fun h => apartNE _ _ ⟨nElbow,h⟩
  have eMissingR : ¬E.Inside (1543/500) 2 :=
    fun h => apartER _ _ ⟨h,rMarker⟩
  have eMissingP : ¬E.Inside 3 1 := fun h => apartEC _ _ ⟨h,cCorner⟩
  have eMissingH : ¬E.Inside (1543/500) 1 := fun h => apartEC _ _ ⟨h,cMarker⟩
  have nPoint := CommonCases.InwardPoint.point_original (pullY N) side
    (by norm_num [inside_pullY]; exact nMarker)
    (by norm_num [inside_pullY]; exact nInward)
    (by norm_num [inside_pullY]; exact nElbow)
    (by norm_num [inside_pullY]; exact nMissingNW)
    (by norm_num [inside_pullY]; exact nMissingSE)
    (by norm_num [inside_pullY]; exact nMissingTop)
  have eSide : 1 < E.side := by simpa only [←same] using side
  have ePoint := CommonCases.OutwardPoint.point_original (pullY E) eSide
    (by norm_num [inside_pullY]; exact eMarker)
    (by norm_num [inside_pullY]; exact eOutward)
    (by norm_num [inside_pullY]; exact eUpper)
    (by norm_num [inside_pullY]; exact eMissingG)
    (by norm_num [inside_pullY]; exact eMissingR)
    (by norm_num [inside_pullY]; exact eMissingP)
    (by norm_num [inside_pullY]; exact eMissingH)
    (by
      intro z lower upper own
      have foreign := bottomBar z lower upper
      have own' : E.Inside z 1 := by norm_num [inside_pullY] at own; exact own
      exact apartEB z 1 ⟨own',foreign⟩)
  norm_num [inside_pullY] at nPoint ePoint
  exact apartNE (123/50) (201/100) ⟨nPoint,ePoint⟩

#print axioms inward_outward_impossible
end N12Compact.Completion.OtherCases.C983

