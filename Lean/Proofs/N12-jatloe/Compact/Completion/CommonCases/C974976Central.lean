import Compact.Completion.OtherCases.C1090.NESelection
import Compact.Completion.OtherCases.OutwardBarFrame
import Compact.Completion.OtherCases.OutwardPair
import Compact.Completion.OtherCases.UpperBarPoint
import Compact.Completion.OtherCases.CrossedElbow
import Compact.Completion.OtherCases.ElbowPoint

/-! Shared continuous C974/C976 central reduction. Every omitted point
and whole foreign segment is explicit in its original coordinates. The
family adapters supply their actual owners; no packing symmetry, exact
auxiliary label, canonical sign or derived support face is assumed. -/
namespace N12Compact.CommonCases.C974976Central
open S12 S12Pilot
open N12Compact.Completion.OtherCases C1092WallProfileScalars
set_option Elab.async false
noncomputable section

theorem southeast_g8 (S N : OpenSquare) (side : 1<S.side)
    (marker : S.Inside (47/20) (33/20)) (f8 : S.Inside 3 (87/50))
    (cover : S.Inside (113/50) 2 ∨ S.Inside 3 (8/5))
    (north : N.Inside (47/20) (47/20))
    (apart : ∀ x y,¬(S.Inside x y ∧ N.Inside x y))
    (south : ¬S.Inside 2 (3/2))
    (right : ¬S.Inside (1543/500) 2) : S.Inside 3 (8/5) := by
  by_contra missing
  exact south (ElbowPoint.points_original S side marker
    (cover.resolve_right missing) f8 (fun own => apart _ _ ⟨own,north⟩)
    missing right).1

structure Input (S N : OpenSquare) : Prop extends toNEInput : C1090.NESelection.Input S N where
  same : S.side=N.side
  southwest : ¬S.Inside 2 (3/2)
  topMarker : ¬N.Inside 2 (1543/500)

theorem northeast_g7 (S N : OpenSquare) (h : Input S N) :
    N.Inside (113/50) 3 := C1090.NESelection.g7 S N h.toNEInput

theorem outward_sharp (S N : OpenSquare) (h : Input S N)
    (missing : ¬S.Inside (113/50) 2) : S.Inside (101/40) (17/8) := by
  have point := OutwardBarPoint.point_original (pullY S) h.sideS
    (by norm_num [inside_pullY]; exact h.markerS)
    (by norm_num [inside_pullY]; exact h.f8)
    (by norm_num [inside_pullY]; exact h.g8)
    (by norm_num [inside_pullY]; exact missing)
    (by norm_num [inside_pullY]; exact h.rightMarker)
    (by norm_num [inside_pullY]; exact h.corner)
    (by norm_num [inside_pullY]; exact h.cornerMarker)
    (by intro x low high own; norm_num [inside_pullY] at own; exact h.bottom x low high own)
  norm_num [inside_pullY] at point
  exact point

theorem northeast_f7 (S N : OpenSquare) (h : Input S N) : N.Inside (12/5) 3 := by
  by_contra missing
  have f5 := h.fCover.resolve_right missing
  have pair := ElbowPoint.points_original (pullSwap (pullX N)) h.sideE
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.markerE)
    (by norm_num [inside_pullSwap,inside_pullX]; exact f5)
    (by norm_num [inside_pullSwap,inside_pullX]; exact northeast_g7 S N h)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northwest)
    (by norm_num [inside_pullSwap,inside_pullX]; exact missing)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.topMarker)
  norm_num [inside_pullSwap,inside_pullX] at pair
  by_cases g6 : S.Inside (113/50) 2
  · exact CrossedElbow.impossible_original S (4/5) h.sideS (by norm_num) le_rfl
      h.markerS g6 h.f8 (fun own => h.apart _ _ ⟨own,pair.1⟩) h.southwest
      (by norm_num; exact h.bottom _ (by norm_num) le_rfl)
  · exact h.apart _ _ ⟨outward_sharp S N h g6,pair.2⟩

theorem top_pair (S N T : OpenSquare) (h : Input S N)
    (apart : ∀ x y,¬(N.Inside x y ∧ T.Inside x y))
    (cover : T.Inside (113/50) 3 ∨ (T.Inside (8/5) 3 ∧ T.Inside (87/50) 3)) :
    T.Inside (8/5) 3 ∧ T.Inside (87/50) 3 := by
  rcases cover with wrong | pair
  · exact False.elim (apart _ _ ⟨northeast_g7 S N h,wrong⟩)
  · exact pair

/-- These two additional exclusions and the whole actual right bar are
supplied after the earlier top-origin argument, avoiding any circular
use of the final southeast inward point. -/
structure EndingInput (S N : OpenSquare) : Prop extends Input S N where
  topOrigin : ¬N.Inside 2 3
  northeastCorner : ¬N.Inside 3 3
  rightBar : ∀ y : ℝ,113/50≤y → y≤64/25 → ¬N.Inside 3 y

theorem outward_frame (S N : OpenSquare) (h : Input S N)
    (missing : ¬S.Inside (113/50) 2) :
    ∃ r : OpenSquare,0<r.c ∧ 0≤r.s ∧ r.s≤r.c ∧ r.side=S.side ∧
      (∀ x y,r.Inside x y↔(pullY S).Inside x y) ∧
      OutwardBarPoint.Faces (r.translated 2 2) :=
  OutwardBarFrame.frame_original (pullY S) h.sideS
    (by norm_num [inside_pullY]; exact h.markerS)
    (by norm_num [inside_pullY]; exact h.f8)
    (by norm_num [inside_pullY]; exact h.g8)
    (by norm_num [inside_pullY]; exact missing)
    (by norm_num [inside_pullY]; exact h.rightMarker)
    (by norm_num [inside_pullY]; exact h.corner)
    (by norm_num [inside_pullY]; exact h.cornerMarker)
    (by intro x low high own; norm_num [inside_pullY] at own; exact h.bottom x low high own)

theorem outward_mixed_impossible (S N : OpenSquare) (h : EndingInput S N)
    (missing : ¬S.Inside (113/50) 2) (f5 : N.Inside 2 (113/50)) : False := by
  obtain ⟨r,cp,sn,order,shape,same,faces⟩ := outward_frame S N h.toInput missing
  let A := (pullY r).translated 2 2
  let E := N.translated 2 2
  have aInside (x y : ℝ) : A.Inside x y↔S.Inside (2+x) (2+y) := by
    dsimp only [A]
    rw [inside_translated_iff,inside_pullY,same,inside_pullY,
      show (4:ℝ)-(4-(2+y))=2+y by ring]
  have nInside (x y : ℝ) : E.Inside x y↔N.Inside (2+x) (2+y) :=
    inside_translated_iff N 2 2 x y
  have side : 1<r.side := by simpa only [shape] using h.sideS
  have actualSame : A.side=E.side := shape.trans h.same
  have upperU : A.loU+A.side≤A.c+r.s := by
    have bound := faces.upperU
    dsimp only [A,pullY,OpenSquare.translated] at bound ⊢
    linarith only [bound]
  have lowerV : -A.c+(4/5)*r.s≤A.loV := by
    have bound := faces.upperV
    dsimp only [A,pullY,OpenSquare.translated] at bound ⊢
    linarith only [bound]
  have halfHigh : half A.c r.s<143/500 :=
    SharpPointScalars.half_upper r.c r.s (143/500) cp faces.sinePositive
      r.unit_normal faces.upperSpan
  have halfLow : 13/87<half A.c r.s := by
    have lower := SharpPointScalars.half_lower r.c r.s (37/50)
      cp sn order r.unit_normal faces.lowerSpan
    change 13/87<half r.c r.s
    linarith only [lower]
  have southMarker : A.Inside (7/20) (-7/20) := by
    apply (aInside _ _).mpr; norm_num; exact h.markerS
  have southSharp : A.Inside (21/40) (1/8) := by
    apply (aInside _ _).mpr; norm_num; exact outward_sharp S N h.toInput missing
  apply OutwardPair.impossible A E r.s side actualSame rfl cp sn order
    halfLow halfHigh upperU lowerV southMarker southSharp
  · apply (nInside _ _).mpr; norm_num; exact h.markerE
  · apply (nInside _ _).mpr; norm_num; exact f5
  · apply (nInside _ _).mpr; norm_num; exact northeast_g7 S N h.toInput
  · intro own; apply h.northwest; convert (nInside _ _).mp own using 1 <;> norm_num
  · intro own; apply h.topOrigin; convert (nInside _ _).mp own using 1 <;> norm_num
  · intro own; apply h.northeastCorner; convert (nInside _ _).mp own using 1 <;> norm_num
  · intro x y pair; exact h.apart _ _ ⟨(aInside _ _).mp pair.1,(nInside _ _).mp pair.2⟩

theorem southeast_g6 (S N : OpenSquare) (h : EndingInput S N) :
    S.Inside (113/50) 2 := by
  by_contra missing
  by_cases f5 : N.Inside 2 (113/50)
  · exact outward_mixed_impossible S N h missing f5
  · have north := UpperBarPoint.point_original N h.sideE h.markerE
      (h.fCover.resolve_left f5) f5 h.topOrigin h.northeastCorner h.rightBar
    exact h.apart _ _ ⟨outward_sharp S N h.toInput missing,north⟩

end
#print axioms northeast_f7
#print axioms southeast_g6
end N12Compact.CommonCases.C974976Central
