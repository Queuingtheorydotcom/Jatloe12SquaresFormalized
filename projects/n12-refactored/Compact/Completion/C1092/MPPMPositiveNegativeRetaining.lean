import Compact.Completion.C1092.MPPMPositiveNegativeRetainingSupport
import Compact.Geometry.ClosedPointExclusion

/-! POSITIVE-NEGATIVE-RETAINING-SHALLOW Theorem 1. The actual successor
vertex is compared with one actual foreign bar, with its endpoint and
tangency cases retained. No extra container wall is assumed. Source only. -/
namespace N12Compact.C1092MPPMPositiveNegativeRetaining
open S12 S12Pilot FourSquareAnchors C977CornerCubic Completion.OtherCases
set_option Elab.async false
noncomputable section

/-- Strict right clearance of the same successor's upper-right closure
vertex. The equality case uses closure exclusion, not strict ownership
of the vertex. -/
theorem right_clearance (C E R : OpenSquare) (h : Input C E R) :
    E.c*(E.loU+E.side)-E.s*(E.loV+E.side)<1 := by
  let J := E.loU+E.side
  let D := E.loV+E.side
  let X := E.c*J-E.s*D
  let Y := E.s*J+E.c*D
  have en := h.targetNormal
  have eb := normal_bounds en
  have dp : 0<E.c := by linarith only [eb.1]
  have tp := negative C E R h
  have high := height_envelope C E R h
  have envelope : -E.loU<(43/500)*E.c-(-E.s)/2 := by linarith only [high]
  have forward : -(13/50)*(-E.s)< -E.loU := by linarith only [h.forward.1]
  have prelim := Scalars.preliminary en forward envelope
  have side : 1<E.side := by linarith only [h.side,h.same]
  have floor : E.side-E.c≤D := by dsimp [D]; linarith only [h.faces.lowerV]
  have upper : J≤E.c-E.s := h.faces.upperU
  have cap : D≤-E.s/2 := next_face C E R h
  have closed : ClosedInside E X Y := by
    apply WallProfile.vertex E J D
    · dsimp [J]; exact ⟨by linarith only [E.side_pos],le_rfl⟩
    · dsimp [D]; exact ⟨by linarith only [E.side_pos],le_rfl⟩
  have yLower : -(23/50)<Y := by
    have first := mul_le_mul_of_nonneg_left floor dp.le
    have second := mul_le_mul_of_nonneg_left upper tp.le
    have sideProduct := mul_pos (sub_pos.mpr side) dp
    have dt := mul_le_mul_of_nonneg_right eb.2.1 tp.le
    dsimp [Y]
    nlinarith only [first,second,sideProduct,dt,en.2.2,prelim.2.1,prelim.2.2]
  have coordinates : E.c*Y=D+E.s*X := by
    dsimp [X,Y]
    linear_combination D*E.unit_normal
  change X<1
  by_contra no
  have xl : 1≤X := by linarith only [no]
  have yUpper : Y<0 := by
    have product := mul_le_mul_of_nonneg_left xl tp.le
    have scaled : E.c*Y<0 := by nlinarith only [coordinates,cap,product,tp]
    by_contra bad
    have nonnegative := mul_nonneg dp.le (show 0≤Y by linarith only [bad])
    linarith only [scaled,nonnegative]
  by_cases edge : X=1
  · have foreign : ClosedInside E 1 Y := by simpa only [edge] using closed
    have excluded := ClosedPointExclusion.outside_of_closed R E 1 Y
      (fun x y own => h.apartER x y ⟨own.2,own.1⟩) foreign
    exact excluded (h.bar Y (by linarith only [yLower]) yUpper.le)
  · have xp : 0<X := by linarith only [xl]
    have strictX : 1<X := by
      rcases eq_or_lt_of_le xl with eq | lt
      · exact (edge eq.symm).elim
      · exact lt
    let z := (X-1)/X
    have zp : 0<z := div_pos (sub_pos.mpr strictX) xp
    have zh : z<1 := (div_lt_iff₀ xp).mpr (by linarith)
    have zx : z*X=X-1 := div_mul_cancel₀ _ xp.ne'
    have remaining : 0≤1-z := by linarith only [zh]
    let v := (1-z)*Y+z*(-13/50)
    have vl : -(14/25)≤v := by
      have first := mul_nonneg remaining (show 0≤Y+14/25 by linarith only [yLower])
      have second := mul_nonneg zp.le (show (0:ℝ)≤14/25-13/50 by norm_num)
      dsimp [v]
      nlinarith only [first,second]
    have vh : v≤0 := by
      have first := mul_nonpos_of_nonneg_of_nonpos remaining yUpper.le
      have second := mul_nonpos_of_nonneg_of_nonpos zp.le (show (-13/50:ℝ)≤0 by norm_num)
      dsimp [v]
      linarith only [first,second]
    have point := WallProfile.strict_closed_segment E X Y 0 (-13/50) z closed h.forward zp zh
    have first : (1-z)*X+z*0=1 := by nlinarith only [zx]
    have own : E.Inside 1 v := by simpa only [first] using point
    exact h.apartER 1 v ⟨own,h.bar v vl vh⟩

/-- The actual bar gives the strict lower height bound from the same
faces that enter height_envelope. -/
theorem height_lower (C E R : OpenSquare) (h : Input C E R) :
    E.c-E.s-1+E.c*E.s<E.c*(-E.loU) := by
  have en := h.targetNormal
  have eb := normal_bounds en
  have dp : 0<E.c := by linarith only [eb.1]
  have tp := negative C E R h
  have clearance := right_clearance C E R h
  have floor := mul_le_mul_of_nonneg_left h.faces.lowerV tp.le
  have side : 1<E.side := by linarith only [h.side,h.same]
  have gap := mul_pos (sub_pos.mpr side)
    (show 0<E.c-E.s by linarith only [dp,tp])
  nlinarith only [clearance,floor,gap]

/-- Full local conclusion, including the strict negative sign produced
from the actual preceding-origin face and actual ordinary point. -/
theorem profile (C E R : OpenSquare) (h : Input C E R) : Profile E := by
  have en := h.targetNormal
  have eb := normal_bounds en
  have dp : 0<E.c := by linarith only [eb.1]
  have tp := negative C E R h
  have high := height_envelope C E R h
  have upper : -E.loU<(43/500)*E.c-(-E.s)/2 := by linarith only [high]
  have forward : -(13/50)*(-E.s)< -E.loU := by linarith only [h.forward.1]
  have prelim := Scalars.preliminary en forward upper
  have low := height_lower C E R h
  have lower : E.c+(-E.s)-1-E.c*(-E.s)<E.c*(-E.loU) := by linarith only [low]
  have result := Scalars.sharpen en tp prelim.2.1 prelim.2.2 upper lower
  exact ⟨tp,(div_lt_iff₀ dp).mpr (by linarith only [result.1]),
    result.2.1,result.2.2.1,result.2.2.2⟩

end
end N12Compact.C1092MPPMPositiveNegativeRetaining
