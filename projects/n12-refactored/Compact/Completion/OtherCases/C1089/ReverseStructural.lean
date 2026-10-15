import Compact.Completion.OtherCases.C1089.ReversePrefix
import Compact.Completion.OtherCases.C1090.ResidualEnding
import Compact.Completion.OtherCases.OutwardBarFrame
import Compact.Completion.OtherCases.OutwardPair
import Compact.Completion.OtherCases.UpperBarPoint
import Compact.Completion.OtherCases.CrossedElbow

/-! The five continuous exclusions on the actual C1089 reverse-sector table,
using the same actual owners as its early reductions. The literal point
antecedents are sufficient; no numeric auxiliary label or pose is assumed.
The northwest marker remains in Q7, and the actual left owner
retains only its own marker and its proved F0/G0 pair. Each bar is the strict bar already derived in its single owner.
This is source translation only, not a compilation or finite-entrance receipt. -/
namespace N12Compact.Completion.OtherCases.C1089.Reverse
open S12 S12Pilot
open C1092WallProfileScalars
set_option Elab.async false
noncomputable section

/-- The surviving F alternative is a literal local covering consequence:
the third original choice F9 belongs to actual Q10. -/
theorem northeast_f5_or_f7 (q : Fin 12 → OpenSquare) (h : PointTable q) :
    (q 6).Inside 2 (113/50) ∨ (q 6).Inside (12/5) 3 := by
  rcases h.northeastFCover with f5 | f7 | f9
  · exact Or.inl f5
  · exact Or.inr f7
  · exact False.elim (h.apart 6 10 (by decide) _ _ ⟨f9,h.rightF9⟩)

/-- An outward S obtains the sharp point from the actual whole bottom
bar, its actual paired corner, and the actual right marker. -/
theorem southeast_outward_point (q : Fin 12 → OpenSquare) (h : PointTable q)
    (missing : ¬(q 5).Inside (113/50) 2) : (q 5).Inside (101/40) (17/8) := by
  have point := OutwardBarPoint.point_original (pullY (q 5)) (h.side 5)
    (by norm_num [inside_pullY]; exact h.southeastMarker)
    (by norm_num [inside_pullY]; exact h.southeastF8)
    (by norm_num [inside_pullY]; exact h.southeastG8)
    (by norm_num [inside_pullY]; exact missing)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 10 (by decide) _ _ ⟨own,h.rightMarker⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCornerRight⟩)
    (by
      intro x low high own
      norm_num [inside_pullY] at own
      exact h.apart 5 9 (by decide) _ _ ⟨own,h.bottomBar x low high⟩)
  norm_num [inside_pullY] at point
  exact point

/-- The same physical S also supplies its derived angle and face bounds.
No support inequality or canonical sign is added to the actual input. -/
theorem southeast_outward_frame (q : Fin 12 → OpenSquare) (h : PointTable q)
    (missing : ¬(q 5).Inside (113/50) 2) :
    ∃ r : OpenSquare,0<r.c ∧ 0≤r.s ∧ r.s≤r.c ∧ r.side=(q 5).side ∧
      (∀ x y,r.Inside x y↔(pullY (q 5)).Inside x y) ∧
      OutwardBarPoint.Faces (r.translated 2 2) :=
  OutwardBarFrame.frame_original (pullY (q 5)) (h.side 5)
    (by norm_num [inside_pullY]; exact h.southeastMarker)
    (by norm_num [inside_pullY]; exact h.southeastF8)
    (by norm_num [inside_pullY]; exact h.southeastG8)
    (by norm_num [inside_pullY]; exact missing)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 10 (by decide) _ _ ⟨own,h.rightMarker⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCorner⟩)
    (by norm_num [inside_pullY]; exact fun own =>
      h.apart 5 1 (by decide) _ _ ⟨own,h.southeastCornerRight⟩)
    (by
      intro x low high own
      norm_num [inside_pullY] at own
      exact h.apart 5 9 (by decide) _ _ ⟨own,h.bottomBar x low high⟩)

/-- The upper-span point uses F7 and omission of F5. It remains valid
whether or not the same northeast owner also owns G6. -/
theorem northeast_upper_point (q : Fin 12 → OpenSquare) (h : PointTable q)
    (f7 : (q 6).Inside (12/5) 3) (missingF5 : ¬(q 6).Inside 2 (113/50)) :
    (q 6).Inside (101/40) (17/8) :=
  UpperBarPoint.point_original (q 6) (h.side 6) h.northeastMarker f7 missingF5
    (fun own => h.apart 6 11 (by decide) _ _ ⟨own,h.topOrigin⟩)
    (fun own => h.apart 6 2 (by decide) _ _ ⟨own,h.northeastCorner⟩)
    (fun y low high own => h.apart 6 10 (by decide) _ _ ⟨own,h.rightBar y low high⟩)

/-- The quarter-turn of the elbow theorem is applied to all point data,
including the original northwest and top markers in their actual owners. -/
theorem northeast_elbow_points (q : Fin 12 → OpenSquare) (h : PointTable q)
    (f5 : (q 6).Inside 2 (113/50)) (missingF7 : ¬(q 6).Inside (12/5) 3) :
    (q 6).Inside (5/2) 2 ∧ (q 6).Inside (101/40) (17/8) := by
  have points := ElbowPoint.points_original (pullSwap (pullX (q 6))) (h.side 6)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northeastMarker)
    (by norm_num [inside_pullSwap,inside_pullX]; exact f5)
    (by norm_num [inside_pullSwap,inside_pullX]; exact h.northeastG7)
    (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
      h.apart 6 7 (by decide) _ _ ⟨own,h.northwestMarker⟩)
    (by norm_num [inside_pullSwap,inside_pullX]; exact missingF7)
    (by norm_num [inside_pullSwap,inside_pullX]; exact fun own =>
      h.apart 6 11 (by decide) _ _ ⟨own,h.topMarker⟩)
  norm_num [inside_pullSwap,inside_pullX] at points
  exact points

/-- First row: the northeast F5/G7 elbow omitting F7 is impossible.
The nonoutward S branch uses crossed-elbow Theorem 2 at the closed w=.8
endpoint; the two other exclusions are in actual E and A. -/
theorem northeast_elbow_impossible (q : Fin 12 → OpenSquare) (h : PointTable q)
    (f5 : (q 6).Inside 2 (113/50)) (missingF7 : ¬(q 6).Inside (12/5) 3) : False := by
  have pair := northeast_elbow_points q h f5 missingF7
  by_cases g6 : (q 5).Inside (113/50) 2
  · exact CrossedElbow.impossible_original (q 5) (4/5) (h.side 5)
      (by norm_num) le_rfl h.southeastMarker g6 h.southeastF8
      (fun own => h.apart 5 6 (by decide) _ _ ⟨own,pair.1⟩)
      (fun own => h.apart 5 4 (by decide) _ _ ⟨own,h.southwestSouth⟩)
      (by
        norm_num
        exact fun own => h.apart 5 9 (by decide) _ _ ⟨own,h.bottomAdvance⟩)
  · exact h.apart 5 6 (by decide) _ _ ⟨southeast_outward_point q h g6,pair.2⟩

/-- Second row: E's optional G6 forces S to omit that same point.
Its missing-F5 upper span then duplicates the sharp outward S point. -/
theorem northeast_upper_g6_impossible (q : Fin 12 → OpenSquare) (h : PointTable q)
    (f7 : (q 6).Inside (12/5) 3) (g6 : (q 6).Inside (113/50) 2)
    (missingF5 : ¬(q 6).Inside 2 (113/50)) : False :=
  h.apart 5 6 (by decide) _ _
    ⟨southeast_outward_point q h (fun own => h.apart 5 6 (by decide) _ _ ⟨own,g6⟩),
      northeast_upper_point q h f7 missingF5⟩

/-- Third row: S's extra F5 is excluded once S owns G6. The F covering
alternative of E gives F7 because the other alternatives have real owners. -/
theorem southeast_f5_impossible (q : Fin 12 → OpenSquare) (h : PointTable q)
    (g6 : (q 5).Inside (113/50) 2) (f5 : (q 5).Inside 2 (113/50)) : False := by
  have missing : ¬(q 6).Inside 2 (113/50) :=
    fun own => h.apart 6 5 (by decide) _ _ ⟨own,f5⟩
  have f7 := (northeast_f5_or_f7 q h).resolve_left missing
  have south := CrossedElbow.point_original (q 5) (h.side 5) h.southeastMarker
    g6 h.southeastF8 f5
    (fun own => h.apart 5 4 (by decide) _ _ ⟨own,h.southwestSouth⟩)
  exact h.apart 5 6 (by decide) _ _ ⟨south,northeast_upper_point q h f7 missing⟩

/-- Fourth row: outward S and a top-only E duplicate the same strict
point. The whole right bar and top origin are derived actual inputs. -/
theorem outward_top_only_impossible (q : Fin 12 → OpenSquare) (h : PointTable q)
    (missingG6 : ¬(q 5).Inside (113/50) 2)
    (f7 : (q 6).Inside (12/5) 3) (missingF5 : ¬(q 6).Inside 2 (113/50)) : False :=
  h.apart 5 6 (by decide) _ _
    ⟨southeast_outward_point q h missingG6,northeast_upper_point q h f7 missingF5⟩

/-- Fifth row: the actual outward S frame and actual mixed E feed the
complete eight-directed-support theorem. No abstract support bounds are
assumed, and E's northwest omission has actual Q7 as its source. -/
theorem outward_mixed_impossible (q : Fin 12 → OpenSquare) (h : PointTable q)
    (missingG6 : ¬(q 5).Inside (113/50) 2)
    (f5 : (q 6).Inside 2 (113/50)) : False := by
  obtain ⟨r,cp,sn,order,shape,same,faces⟩ := southeast_outward_frame q h missingG6
  let A := (pullY r).translated 2 2
  let N := (q 6).translated 2 2
  have aInside (x y : ℝ) : A.Inside x y↔(q 5).Inside (2+x) (2+y) := by
    dsimp only [A]
    rw [inside_translated_iff,inside_pullY,same,inside_pullY,
      show (4:ℝ)-(4-(2+y))=2+y by ring]
  have nInside (x y : ℝ) : N.Inside x y↔(q 6).Inside (2+x) (2+y) :=
    inside_translated_iff (q 6) 2 2 x y
  have side : 1<r.side := by simpa only [shape] using h.side 5
  have actualSame : A.side=N.side := shape.trans (h.same 5 6)
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
    apply (aInside _ _).mpr
    norm_num
    exact h.southeastMarker
  have southSharp : A.Inside (21/40) (1/8) := by
    apply (aInside _ _).mpr
    norm_num
    exact southeast_outward_point q h missingG6
  apply OutwardPair.impossible A N r.s side actualSame rfl cp sn order
    halfLow halfHigh upperU lowerV southMarker southSharp
  · apply (nInside _ _).mpr; norm_num; exact h.northeastMarker
  · apply (nInside _ _).mpr; norm_num; exact f5
  · apply (nInside _ _).mpr; norm_num; exact h.northeastG7
  · intro own
    have actual := (nInside _ _).mp own
    norm_num at actual
    exact h.apart 6 7 (by decide) _ _ ⟨actual,h.northwestMarker⟩
  · intro own
    have actual := (nInside _ _).mp own
    norm_num at actual
    exact h.apart 6 11 (by decide) _ _ ⟨actual,h.topOrigin⟩
  · intro own
    have actual := (nInside _ _).mp own
    norm_num at actual
    exact h.apart 6 2 (by decide) _ _ ⟨actual,h.northeastCorner⟩
  · intro x y both
    exact h.apart 5 6 (by decide) _ _ ⟨(aInside _ _).mp both.1,(nInside _ _).mp both.2⟩

end
#print axioms northeast_elbow_impossible
#print axioms northeast_upper_g6_impossible
#print axioms southeast_f5_impossible
#print axioms outward_top_only_impossible
#print axioms outward_mixed_impossible
end N12Compact.Completion.OtherCases.C1089.Reverse

namespace N12Compact.Completion.OtherCases.C1089.Reverse
open S12 S12Pilot
set_option Elab.async false

/-- The outward S alternative is impossible for either literal northeast
F5 choice. The F7 branch follows from the genuine local F cover. -/
theorem southeast_g6 (q : Fin 12 → OpenSquare) (h : PointTable q) :
    (q 5).Inside (113/50) 2 := by
  by_contra missing
  by_cases f5 : (q 6).Inside 2 (113/50)
  · exact outward_mixed_impossible q h missing f5
  · exact outward_top_only_impossible q h missing
      ((northeast_f5_or_f7 q h).resolve_left f5) f5

/-- Omitting northeast F7 would give the eliminated F5/G7 elbow.
Neither an exact auxiliary label nor an angle choice is used. -/
theorem northeast_f7 (q : Fin 12 → OpenSquare) (h : PointTable q) :
    (q 6).Inside (12/5) 3 := by
  by_contra missing
  exact northeast_elbow_impossible q h
    ((northeast_f5_or_f7 q h).resolve_right missing) missing

/-- The two residual point profiles have the same compulsory F7/G7
in E and F8/G6/G8 in S. E may or may not own F5; S cannot own F5,
and E cannot own G6 because its actual owner is S. This statement does
not identify complete auxiliary labels beyond these proved memberships. -/
theorem central_points (q : Fin 12 → OpenSquare) (h : PointTable q) :
    (q 5).Inside (113/50) 2 ∧ (q 6).Inside (12/5) 3 ∧
      ¬(q 5).Inside 2 (113/50) ∧ ¬(q 6).Inside (113/50) 2 := by
  have sg6 := southeast_g6 q h
  exact ⟨sg6,northeast_f7 q h,
    fun own => southeast_f5_impossible q h sg6 own,
    fun own => h.apart 6 5 (by decide) _ _ ⟨own,sg6⟩⟩

theorem residual_input (q : Fin 12 → OpenSquare) (h : PointTable q)
    (southeastG6 : (q 5).Inside (113/50) 2)
    (northeastF7 : (q 6).Inside (12/5) 3) : C1090.Residual.Input q where
  side := h.side
  same := h.same
  box := h.box
  apart := h.apart
  singletonNear := h.singletonNear
  singletonFar := h.singletonFar
  southeastCornerMarker := h.southeastCornerBottom
  southeastCorner := h.southeastCorner
  northeastCorner := h.northeastCorner
  northwestCornerMarker := h.northwestCornerTop
  northwestCorner := h.northwestCorner
  southwestMarker := h.southwestMarker
  southwestF4 := h.southwestF4
  southwestG3 := h.southwestG3
  southwestWest := h.southwestWest
  southwestSouth := h.southwestSouth
  southeastMarker := h.southeastMarker
  southeastF8 := h.southeastF8
  southeastG6 := southeastG6
  southeastG8 := h.southeastG8
  northeastMarker := h.northeastMarker
  northeastF7 := northeastF7
  northeastG7 := h.northeastG7
  northwestMarker := h.northwestMarker
  northwestF1 := h.northwestF1
  northwestG1 := h.northwestG1
  leftMarker := h.leftMarker
  leftF0 := h.leftF0
  leftG0 := h.leftG0
  bottomMarker := h.bottomMarker
  bottomF6 := h.bottomF6
  bottomG5 := h.bottomG5
  bottomAdvance := h.bottomAdvance
  rightF9 := h.rightF9
  rightAdvance := h.rightAdvance
  topMarker := h.topMarker
  topF3 := h.topF3
  topG4 := h.topG4

/-- The full original reverse sector, with no merged-marker premise and
no globally missing marker reassigned to an actual square. -/
theorem impossible (p : NormalizedPacking) (hf : codedMarkerFamily p=OriginalData.family)
    (left : centerY (OriginalData.owners p 8)≤2)
    (top : centerX (OriginalData.owners p 11)≤2) : False := by
  have h := point_table p hf left top
  exact C1090.Residual.impossible _
    (residual_input _ h (southeast_g6 _ h) (northeast_f7 _ h))

#print axioms residual_input
#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.Reverse
