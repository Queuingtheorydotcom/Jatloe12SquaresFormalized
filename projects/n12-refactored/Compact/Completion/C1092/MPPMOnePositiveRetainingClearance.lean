import Compact.Completion.C1092.MPPMOnePositiveRetainingAngle
import Compact.Completion.C1092.MPPMAllNonpositiveProfiles

/-! ONE-POSITIVE-CONTINUOUS-ENDING Lemma 3.2.  A strict crosspoint
in the actual next square excludes the point from D; the whole next-wall
bar in one actual B then clears D's lowest closure vertex.  The quarter
turn transports that vertex to the recipient's strict right clearance. -/
namespace N12Compact.C1092MPPMOnePositive
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports Completion.OtherCases C1092MPPMAllNonpositive
set_option Elab.async false
noncomputable section

/-- The clearance uses only the numerical range supplied by the
half-slope reduction, rather than the stronger one-quarter source range. -/
theorem narrow_crosspoint_clearance (C B : OpenSquare) (core : Core C)
    (close : 89/100<C.c) (small : -C.s<9/20)
    (foreign : ¬C.Inside 0 (-1/2))
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ B.Inside x y)) :
    C.loU+C.side≤-C.s/2 ∧ -1<C.s*(C.loU+C.side)+C.c*C.loV := by
  have f := faces C core
  have cb := normal_bounds core.normal
  have cp : 0<C.c := by linarith only [close]
  have sp : 0< -C.s := by linarith only [f.negative]
  have cap : C.loU+C.side≤-C.s/2 := by
    apply le_of_not_gt
    intro high
    apply foreign
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [high,core.ordinary.1,core.forward.2.2.2,f.upperV,
        core.side,cb.2.1,cp,sp,core.normal.2.1]
  have lowerV : -C.c+(14/25)*C.s≤C.loV := by
    apply le_of_not_gt
    intro low
    apply apart (-14/25) (-1)
    refine ⟨?_,bar _ (by norm_num) (by norm_num)⟩
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,core.ordinary.1,core.ordinary.2.2.2,f.lowerU,
        core.side,cb.2.1,cp,sp,small,core.normal.2.1]
  let A := C.loU+C.side
  let X := C.c*A-C.s*C.loV
  let Y := C.s*A+C.c*C.loV
  have closed : ClosedInside C X Y := WallProfile.vertex C A C.loV
    ⟨by dsimp [A]; linarith only [C.side_pos],le_rfl⟩
    ⟨le_rfl,by linarith only [C.side_pos]⟩
  have first := mul_nonneg cp.le (sub_nonneg.mpr f.lowerU)
  have second := mul_nonneg sp.le (sub_nonneg.mpr lowerV)
  have excess := mul_pos cp (sub_pos.mpr core.side)
  have cross := mul_nonneg sp.le (show 0≤1-C.c by linarith only [cb.2.1])
  have xl : -14/25<X := by
    dsimp [X,A]
    nlinarith only [first,second,excess,cross,close,small,C.unit_normal,sq_nonneg C.s]
  have height : -1<Y := by
    apply lt_of_not_ge
    intro below
    have identity : C.c*X+C.s*Y=A := by
      dsimp [X,Y]
      linear_combination A*C.unit_normal
    have product := mul_nonneg sp.le (show 0≤-1-Y by linarith only [below])
    have scaled : C.c*X≤0 := by
      dsimp [A] at identity
      nlinarith only [identity,product,cap,sp]
    have xu : X≤0 := by
      apply le_of_not_gt
      intro bad
      have positive := mul_pos cp bad
      linarith only [scaled,positive]
    exact (not_lt_of_ge below) (above_bar C B X Y closed core.forward xl.le xu bar apart)
  exact ⟨cap,height⟩

/-- E is one fixed clockwise turn of D.  Its rightmost vertex comes
from D's lowest vertex, with strict clearance retained at contact. -/
theorem retaining_successor_cleared (C D B : OpenSquare)
    (h : RetainingPairInput C (C1092MMMPEndingAxes.clockwise D))
    (core : Core D) (foreign : ¬D.Inside 0 (-1/2))
    (bar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (apart : ∀ x y,¬(D.Inside x y ∧ B.Inside x y)) :
    ClearedSuccessor (C1092MMMPEndingAxes.clockwise D) := by
  have bounds := retaining_successor_bounds C _ h
  have clearance := narrow_crosspoint_clearance D B core bounds.1 bounds.2 foreign bar apart
  have f := faces D core
  have cb := normal_bounds core.normal
  have strictCosine : D.c<1 := by
    nlinarith only [D.unit_normal,f.negative,sq_pos_of_neg f.negative,cb.2.1]
  refine ⟨core.normal,f.lowerU,?_,?_,f.negative,strictCosine,?_⟩
  · change 873/1000<D.c
    linarith only [bounds.1]
  · change -D.s<61/125
    linarith only [bounds.2]
  · change D.c*(-D.loV-D.side+D.side)-D.s*(D.loU+D.side)<1
    linarith only [clearance.2]

end
#print axioms narrow_crosspoint_clearance
#print axioms retaining_successor_cleared
end N12Compact.C1092MPPMOnePositive
