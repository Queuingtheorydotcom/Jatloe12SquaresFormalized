import Compact.Completion.C1092.MPPMInwardFinalBarProfile
import Compact.Completion.C1092.MPPMPositiveRetainingSteepScalars

/-! CENTERED-INWARD-OMITTED-G-FAR-ENDING section 1. The entire far
right bar caps one actual negative successor, independently of a bottom
origin. The closed vertex is used only to produce a strict crossing.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardOmittedFar
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
open C1092MPPMInwardFinal Completion.OtherCases
set_option Elab.async false
noncomputable section

private theorem narrow_support {d t : ℝ} (en : Normal d t)
    (narrow : half d t<3/10) : t+(263/500)*d<1 := by
  have eb := normal_bounds en
  have data := quarter_data d t (by linarith only [eb.1]) en.1 en.2.2
  let z := half d t
  have zn : 0≤z := data.1
  have zh : z<3/10 := narrow
  have product := mul_nonneg (show 0≤3/10-z by linarith only [zh])
    (show 0≤2-(763/500)*(z+3/10) by linarith only [zh])
  have scalar : 0<237/500+(763/500)*z^2-2*z := by nlinarith only [product]
  have identity : (1+z^2)*(1-t-(263/500)*d)=237/500+(763/500)*z^2-2*z := by
    linear_combination -(263/500)*data.2.2.2.1-data.2.2.2.2
  have positive : 0<(1+z^2)*(1-t-(263/500)*d) := by rw [identity]; exact scalar
  have gap := pos_of_mul_pos_right positive (show 0≤1+z^2 by positivity)
  linarith only [gap]

private theorem crossing_right (E R : OpenSquare) (X Y : ℝ)
    (closed : ClosedInside E X Y) (marker : E.Inside (7/20) (-7/20))
    (right : 1<X) (low : -14/25<Y) (high : Y<0)
    (bar : ∀ y : ℝ,-14/25≤y → y≤0 → R.Inside 1 y)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) : False := by
  let z := (X-1)/(X-7/20)
  have den : 0<X-7/20 := by linarith only [right]
  have zp : 0<z := div_pos (by linarith only [right]) den
  have zu : z<1 := (div_lt_one den).mpr (by linarith)
  have relation : z*(X-7/20)=X-1 := div_mul_cancel₀ _ den.ne'
  have coordinate : (1-z)*X+z*(7/20)=1 := by nlinarith only [relation]
  have lower := mul_nonneg (show 0≤1-z by linarith only [zu])
    (show 0≤Y+14/25 by linarith only [low])
  have upper := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤1-z by linarith only [zu]) high.le
  have point := WallProfile.strict_closed_segment E X Y (7/20) (-7/20) z
    closed marker zp zu
  rw [coordinate] at point
  exact apart _ _ ⟨point,bar _ (by nlinarith only [lower,zp]) (by nlinarith only [upper,zp])⟩

/-- Reusable far cap, with no bottom-origin premise. The same E retains
all preliminary faces and the same R owns every point of the bar. -/
theorem far_cap (E R : OpenSquare) (side : 1<E.side) (e : NegativeSuccessor E)
    (bar : ∀ y : ℝ,-14/25≤y → y≤0 → R.Inside 1 y)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) :
    E.loV+E.side≤-E.s-(14/25)*E.c ∧ 237/763<half E.c (-E.s) := by
  have en := e.normal
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have tp : 0< -E.s := by linarith only [e.lowerV,e.upperV,side,eb.2.1]
  have missing : ¬E.Inside 1 (-14/25) := fun own =>
    apart _ _ ⟨own,bar _ le_rfl (by norm_num)⟩
  have cap : E.loV+E.side≤-E.s-(14/25)*E.c := by
    by_cases upperU : E.loU+E.side≤E.c-(14/25)*E.s
    · exfalso
      have width : 1<E.c-(3/10)*E.s := by linarith only [e.lowerU,upperU,side]
      have data := quarter_data E.c (-E.s) ep.le en.1 en.2.2
      let z := half E.c (-E.s)
      have identity : (1+z^2)*(E.c-(3/10)*E.s-1)=2*z*(3/10-z) := by
        nlinarith only [data.2.2.2.1,data.2.2.2.2]
      have positive := mul_pos (show 0<1+z^2 by positivity) (sub_pos.mpr width)
      have narrow : z<3/10 := by
        apply lt_of_not_ge
        intro no
        have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*z by linarith only [data.1])
          (show 3/10-z≤0 by linarith only [no])
        nlinarith only [bad,identity,positive]
      have support := narrow_support en narrow
      let J := E.loU+E.side
      let D := E.loV+E.side
      let X := E.c*J-E.s*D
      let Y := E.s*J+E.c*D
      have closed : ClosedInside E X Y := WallProfile.vertex E J D
        ⟨by dsimp [J]; linarith only [E.side_pos],le_rfl⟩
        ⟨by dsimp [D]; linarith only [E.side_pos],le_rfl⟩
      have upperY : Y<0 := by
        have first := mul_nonneg tp.le (sub_nonneg.mpr e.lowerU)
        have top : E.loV+E.side≤-E.s := by linarith only [e.upperV,ep]
        have last := mul_nonneg ep.le (sub_nonneg.mpr top)
        have strict := mul_pos tp (show 0<E.side-E.c by linarith only [side,eb.2.1])
        dsimp [Y,J,D]
        nlinarith only [first,last,strict,sq_nonneg E.s]
      have lowerY : -14/25<Y := by
        have first := mul_nonneg tp.le (sub_nonneg.mpr upperU)
        have last := mul_nonneg ep.le (sub_nonneg.mpr e.lowerV)
        have strict := mul_pos ep (sub_pos.mpr side)
        have gap := mul_pos ep (show 0<1+E.s-(263/500)*E.c by linarith only [support])
        dsimp [Y,J,D]
        nlinarith only [first,last,strict,gap,E.unit_normal]
      have right : 1<X := by
        have first := mul_nonneg ep.le (sub_nonneg.mpr e.lowerU)
        have last := mul_nonneg tp.le (sub_nonneg.mpr e.lowerV)
        have strict := mul_pos (sub_pos.mpr side)
          (show 0<E.c-E.s by linarith only [ep,tp])
        have cb := C1092MPPMPositiveRetainingSteep.Scalars.canonical_bounds en
        have chord := mul_nonneg
          (show 0≤71/50-(E.c-E.s) by linarith only [cb.2.2.2.2])
          (show 0≤E.c-E.s-1 by linarith only [eb.2.2.2.2.1])
        have arc : 1-(100/121)*E.c*E.s≤E.c-E.s := by
          nlinarith only [chord,E.unit_normal]
        have cross := mul_pos ep tp
        dsimp [X,J,D]
        nlinarith only [first,last,strict,arc,cross]
      exact crossing_right E R X Y closed e.marker right lowerY upperY bar apart
    · apply le_of_not_gt
      intro high
      apply missing
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [upperU,high,e.marker.1,e.outer.2.2.1,ep,tp]
  have angle := width_half (263/500) en (by norm_num)
    (show 1< -E.s+(263/500)*E.c by linarith only [cap,e.lowerV,side])
  exact ⟨cap,by norm_num at angle; exact angle⟩

end
end N12Compact.C1092MPPMInwardOmittedFar
