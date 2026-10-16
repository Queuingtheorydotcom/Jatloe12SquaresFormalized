import S12.SquareFrame
import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.C977CornerCubic

/-! `C1092-MPPM-MISSING-POSITIVE-WALL-ORDER.md`, Lemma 1.
All four faces and the strict half-angle entrance are derived from literal
strict points and point absences. No preceding wall origin, foreign owner
for the omitted forward point, or support inequality is assumed.

The small-angle subargument uses a unit-circle chord in place of the prose
half-angle factor: c+.086s>1 implies s<.172, hence .826c+s<1.
This is written Lean source; no compiler or replay has been run. -/
namespace N12Compact.C1092MPPMMissingPositiveFaces
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure Inputs (C : OpenSquare) : Prop where
  marker : C.Inside (-7/20) (-7/20)
  ordinaryP : C.Inside (-1) (-13/50)
  ordinaryG : C.Inside (-1) (-2/5)
  halfpoint : C.Inside (-1) (-1/2)
  corner : ¬C.Inside (-1) (-1)
  cornerMarker : ¬C.Inside (-543/500) (-1)
  wallMarker : ¬C.Inside (-543/500) 0
  forward : ¬C.Inside (-13/50) 0
  farBottom : ¬C.Inside (-14/25) (-1)
  innerBottom : ¬C.Inside (-13/50) (-1)

structure Faces (C : OpenSquare) : Prop where
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤-(13/50)*C.c
  lowerV : (14/25)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤(543/500)*C.s
  positive : 0<C.s
  halfLow : 13/87<C1092WallProfileScalars.half C.c C.s
  halfHigh : C1092WallProfileScalars.half C.c C.s<1/2
  widthU : C.side≤(37/50)*C.c+C.s
  widthV : C.side≤C.c+(263/500)*C.s

private theorem short_after_thin_width {c s : ℝ} (cn : Normal c s)
    (width : 1<c+(43/500)*s) : (413/500)*c+s<1 := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := by linarith only [width,cb.2.1]
  have product := mul_pos (show 0<c+(43/500)*s-1 by linarith only [width])
    (show 0<c+1 by linarith only [cp])
  have identity : (c+(43/500)*s-1)*(c+1)=s*((43/500)*(1+c)-s) := by
    linear_combination cn.2.2
  rw [identity] at product
  have gap : 0<(43/500)*(1+c)-s := by
    by_contra failure
    have bad := mul_nonpos_of_nonneg_of_nonpos sp.le (le_of_not_gt failure)
    linarith only [product,bad]
  have small : s<43/250 := by linarith only [gap,cb.2.1]
  linarith only [small,cb.2.1]

/-- A complete point-to-face producer on the whole nonnegative canonical
interval. Strict ownership defeats every excluded-face alternative; an
excluded point itself is never promoted to a strict point. -/
theorem profile (C : OpenSquare) (side : 1<C.side)
    (cn : Normal C.c C.s) (h : Inputs C) : Faces C := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have upperU : C.loU+C.side≤-(13/50)*C.c := by
    apply le_of_not_gt
    intro high
    have upperV : C.loV+C.side≤(13/50)*C.s := by
      apply le_of_not_gt
      intro highV
      apply h.forward
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [h.ordinaryP.1,h.marker.2.2.1,high,highV,cp,cn.1,cn.2.1]
    have lowerU : -C.c-C.s≤C.loU := by
      apply le_of_not_gt
      intro low
      have cornerV : C.s-C.c≤C.loV := by
        apply le_of_not_gt
        intro lowV
        apply h.corner
        refine ⟨?_,?_,?_,?_⟩ <;>
          linarith only [low,lowV,h.halfpoint.2.1,h.halfpoint.2.2.2,cp,cn.1]
      linarith only [cornerV,upperV,side,cb.2.1,cn.1]
    have innerLowU : C.loU< -(13/50)*C.c-C.s := by
      linarith only [h.ordinaryP.1,cn.2.1]
    have innerLowV : C.loV<(13/50)*C.s-C.c := by
      linarith only [upperV,side,cb.2.1]
    have innerHighV : (13/50)*C.s-C.c<C.loV+C.side := by
      linarith only [h.ordinaryP.2.2.2,cp,cn.1]
    have innerHighU : C.loU+C.side≤-(13/50)*C.c-C.s := by
      apply le_of_not_gt
      intro highU
      apply h.innerBottom
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [innerLowU,highU,innerLowV,innerHighV]
    linarith only [lowerU,innerHighU,side,cb.2.1]
  have upperV : C.loV+C.side≤(543/500)*C.s := by
    apply le_of_not_gt
    intro high
    have lowerU : -(543/500)*C.c≤C.loU := by
      apply le_of_not_gt
      intro low
      apply h.wallMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,h.marker.2.1,h.ordinaryP.2.2.1,cp,cn.1,cn.2.1]
    linarith only [lowerU,upperU,side,cb.2.1]
  have lowerU : -C.c-C.s≤C.loU := by
    apply le_of_not_gt
    intro low
    have lowerV : C.s-C.c≤C.loV := by
      apply le_of_not_gt
      intro lowV
      apply h.corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,lowV,h.halfpoint.2.1,h.halfpoint.2.2.2,cp,cn.1]
    have thin : 1<C.c+(43/500)*C.s := by linarith only [lowerV,upperV,side]
    have short := short_after_thin_width cn thin
    have cornerMarkerV : (543/500)*C.s-C.c≤C.loV := by
      apply le_of_not_gt
      intro lowV
      apply h.cornerMarker
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lowV,upperU,side,short,h.ordinaryP.2.1,
          h.ordinaryP.2.2.2,cp,cn.1,cn.2.1]
    linarith only [cornerMarkerV,upperV,side,cb.2.1]
  have shortFar : (3/10)*C.c+C.s<1 := by
    linarith only [cb.2.2.2.2.2,cn.2.1]
  have lowerV : (14/25)*C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    have farHighU : C.loU+C.side≤-(14/25)*C.c-C.s := by
      apply le_of_not_gt
      intro high
      apply h.farBottom
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,upperU,side,shortFar,h.ordinaryP.2.2.2,cp,cn.1]
    linarith only [farHighU,lowerU,side,cb.2.1]
  have widthU : C.side≤(37/50)*C.c+C.s := by linarith only [lowerU,upperU]
  have widthV : C.side≤C.c+(263/500)*C.s := by linarith only [lowerV,upperV]
  have sp : 0<C.s := by linarith only [widthU,side,cb.2.1]
  let q := C1092WallProfileScalars.half C.c C.s
  have hp : 0<q := by
    dsimp [q,C1092WallProfileScalars.half]
    exact div_pos sp (by linarith only [cp])
  have hh : q<1/2 := by
    dsimp [q,C1092WallProfileScalars.half]
    apply (div_lt_iff₀ (show 0<1+C.c by linarith only [cp])).mpr
    linarith only [cb.2.2.2.2.2,cn.2.1,cb.1]
  have halfData := C1092WallProfileScalars.quarter_data C.c C.s cp.le cn.1 cn.2.2
  have cosine : (1+q^2)*C.c=1-q^2 := halfData.2.2.2.1
  have sine : (1+q^2)*C.s=2*q := halfData.2.2.2.2
  have identity : (1+q^2)*((37/50)*C.c+C.s-1)=
      (1-q)*(87*q-13)/50 := by
    linear_combination (37/50)*cosine+sine
  have positive := mul_pos (show 0<1+q^2 by nlinarith only [sq_nonneg q])
    (show 0<(37/50)*C.c+C.s-1 by linarith only [widthU,side])
  rw [identity] at positive
  have low : 13/87<q := by
    by_contra failure
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-q by linarith only [hh])
      (show 87*q-13≤0 by linarith only [le_of_not_gt failure])
    linarith only [positive,bad]
  exact ⟨lowerU,upperU,lowerV,upperV,sp,low,hh,widthU,widthV⟩

#print axioms profile
end N12Compact.C1092MPPMMissingPositiveFaces
