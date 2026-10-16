import Compact.Completion.C1092.MMMMFirstPair
import S12.ShortCluster

/-! The positive northeast faces before any top-origin deduction. Every
exit is supplied by a genuine omitted point, including the actual G9
owner at (-.4,1); no lower face at the top origin is assumed. -/
namespace N12Compact.C1092MMMPNortheastEarlyFaces
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

structure Data (B : OpenSquare) : Prop where
  lowerU : -(543/500)*B.c≤B.loU
  upperU : B.loU+B.side≤B.s-(2/5)*B.c
  lowerV : (2/5)*B.s≤B.loV
  upperV : B.loV+B.side≤B.c+B.s

theorem faces (B : OpenSquare) (side : 1<B.side) (bn : Normal B.c B.s)
    (positive : 0<B.s) (M : B.Inside (-7/20) (7/20))
    (H2 : B.Inside (-1) (2/5))
    (I : ¬B.Inside (-2/5) 0) (J : ¬B.Inside (-2/5) 1)
    (W : ¬B.Inside (-543/500) 0) (K : ¬B.Inside (-1) 1) : Data B := by
  have cb := normal_bounds bn
  have cp : 0<B.c := by linarith only [cb.1]
  have lowerV : (2/5)*B.s≤B.loV := by
    apply le_of_not_gt
    intro low
    apply I
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [H2.1,M.2.1,M.2.2.2,low,cp,positive,bn.2.1]
  have upperU : B.loU+B.side≤B.s-(2/5)*B.c := by
    apply le_of_not_gt
    intro high
    have highV : (2/5)*B.s+B.c<B.loV+B.side := by
      linarith only [lowerV,side,cb.2.1]
    apply J
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [H2.1,M.2.2.1,high,highV,cp,positive,bn.2.1]
  have upperV : B.loV+B.side≤B.c+B.s := by
    apply le_of_not_gt
    intro high
    apply K
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [H2.1,H2.2.2.1,M.2.1,high,cp,positive,bn.2.1]
  have lowerU : -(543/500)*B.c≤B.loU := by
    apply le_of_not_gt
    intro low
    have lowV : B.loV<(543/500)*B.s := by
      linarith only [upperV,side,cb.2.1,positive]
    have highV : (543/500)*B.s<B.loV+B.side := by
      linarith only [lowerV,side,cb.2.2.2.1]
    apply W
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,M.2.1,lowV,highV,cp,positive]
  exact ⟨lowerU,upperU,lowerV,upperV⟩

theorem upper_point (B : OpenSquare) (side : 1<B.side) (f : Data B) :
    B.Inside (-1/2) (7/50) := by
  have one := short_projections B (1/10) (43/50) (by norm_num)
  have two := short_projections B (293/500) (7/50) (by norm_num)
  have three := short_projections B (43/50) (1/2) (by norm_num)
  have four := short_projections B (7/50) (1/10) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [side,f.lowerU,f.upperU,f.lowerV,f.upperV,
      one.2.1,two.2.1,three.2.1,four.2.1]

/-- The retained positive-neighbor support uses only the two upper faces;
the complete central square keeps the same U and V in its angle bound. -/
theorem small_central (C B : OpenSquare) (side : 1<C.side) (same : C.side=B.side)
    (dn : Normal C.c (-C.s)) (bn : Normal B.c B.s) (positive : 0<B.s)
    (origin : C.Inside 0 0) (bottom : C.Inside 0 (-1/2))
    (central : C.Inside (-7/20) (-7/20)) (missing : ¬C.Inside (7/20) (-7/20))
    (marker : B.Inside (-7/20) (7/20)) (H2 : B.Inside (-1) (2/5))
    (f : Data B) (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) :
    -C.s<7/50 ∧ 99/100<C.c := by
  have cb := normal_bounds dn
  have cp : 0<C.c := by linarith only [cb.1]
  have cap : C.loU+C.side≤(7/20)*(C.c-C.s) := by
    apply le_of_not_gt
    intro upper
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upper,origin.1,origin.2.2.2,bottom.2.2.1,cp,dn.1,dn.2.1]
  have support := C1092MMMMFirstPair.positive_support C B side same dn bn positive origin bottom
    central missing marker H2
    (by linarith only [f.upperU,cp,(normal_bounds bn).1]) f.upperV apart
  have cap' : C.loU+C.side≤(7/20)*(C.c+(-C.s)) := by linarith only [cap]
  exact C1092MMMMPairScalars.small_of_support dn bn side
    (by linarith only [origin.2.1]) (by linarith only [origin.2.2.2]) cap' support

#print axioms faces
#print axioms small_central
end N12Compact.C1092MMMPNortheastEarlyFaces
