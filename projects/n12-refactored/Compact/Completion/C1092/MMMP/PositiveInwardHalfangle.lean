import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.C977CornerCubic
import S12.ShortCluster

/-! Transcription of C1092-MMMP-DOUBLE-RIGHT-BOTTOM-ORIGIN, section 1.1,
and its section 5 angle consequence (also RIGHT-NEAR-BOTTOM-ORIGIN, section 4).
The isolated exclusions below are literal point absences. In particular no
foreign segment is inferred between the two isolated upper exclusions.

The whole-boundary support argument in sections 1.2--3 is a separate
obligation: this module does not assert the actual bottom origin. -/
namespace N12Compact.C1092MMMPPositiveInwardHalfangle
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

theorem half_identities (c s : ℝ) (cp : 0<c) (unit : c^2+s^2=1) :
    C1092WallProfileScalars.half c s*(1+c)=s ∧
      s*C1092WallProfileScalars.half c s=1-c := by
  have den : 0<1+c := by linarith only [cp]
  constructor
  · dsimp [C1092WallProfileScalars.half]
    field_simp [den.ne']
  · dsimp [C1092WallProfileScalars.half]
    field_simp [den.ne']
    nlinarith only [unit]

/-- The inward anchors and two genuine exclusions bound the half-angle
strictly below .26, including exclusion of the axial endpoint. -/
theorem entrance (C : OpenSquare) (side : 1<C.side) (cn : Normal C.c C.s)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (A : ¬C.Inside (2/5) 1) (G : ¬C.Inside 1 (13/50)) :
    0≤C.loU ∧ 0<C.s ∧ C.loV+C.side≤C.c-(2/5)*C.s ∧
      0<C1092WallProfileScalars.half C.c C.s ∧
      C1092WallProfileScalars.half C.c C.s<13/50 ∧
      2331/2669<C.c ∧ C.s<1300/2669 := by
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have lower : 0≤C.loU := by
    apply le_of_not_gt
    intro low
    apply O
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,M.2.1,J.2.2.1,I.2.2.2,cp,cn.1]
  have sp : 0<C.s := by nlinarith only [lower,I.1]
  have aShort : (2/5)*C.c+C.s<1 := by
    have gap := mul_nonneg (sub_nonneg.mpr cn.2.1)
      (show 0≤(41/50)*C.c+(1/50)*C.s by linarith only [cp,cn.1])
    have square : ((2/5)*C.c+C.s)^2≤49/50 := by
      nlinarith only [gap,cn.2.2]
    nlinarith only [square,sq_nonneg ((2/5)*C.c+C.s-1)]
  have cap : C.loV+C.side≤C.c-(2/5)*C.s := by
    apply le_of_not_gt
    intro high
    apply A
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [M.1,J.2.2.1,high,aShort,lower,side,cp,cn.1,cn.2.1]
  let z := C1092WallProfileScalars.half C.c C.s
  have zp : 0<z := by
    dsimp [z,C1092WallProfileScalars.half]
    exact div_pos sp (by linarith only [cp])
  have identities := half_identities C.c C.s cp cn.2.2
  have angle : z*(1+C.c)=C.s := identities.1
  have unitAngle : C.s*z=1-C.c := identities.2
  have small : z<13/50 := by
    apply lt_of_not_ge
    intro high
    have weighted := mul_nonneg cn.1 (sub_nonneg.mpr high)
    have short := (short_projections C (37/50) (3/5) (by norm_num)).2.1
    apply G
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [J.1,cp,cn.1]
    · nlinarith only [weighted,unitAngle,lower,side]
    · linarith only [cap,side,short]
    · linarith only [I.2.2.2,sp]
  have cosine : 2331/2669<C.c := by
    have weighted := mul_pos (show 0<13/50-z by linarith only [small])
      (show 0<1+C.c by linarith only [cp])
    have first : 0<13*(1+C.c)-50*C.s := by nlinarith only [weighted,angle]
    have square := mul_pos first
      (show 0<13*(1+C.c)+50*C.s by linarith only [cp,sp])
    apply lt_of_not_ge
    intro bad
    have nonpositive := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1+C.c by linarith only [cp])
      (show 2669*C.c-2331≤0 by linarith only [bad])
    nlinarith only [square,nonpositive,cn.2.2]
  have sine : C.s<1300/2669 := by
    have first := mul_pos (sub_pos.mpr cosine)
      (show 0<C.c+2331/2669 by linarith only [cp])
    apply lt_of_not_ge
    intro bad
    have last := mul_nonneg (show 0≤C.s-1300/2669 by linarith only [bad])
      (show 0≤C.s+1300/2669 by linarith only [sp])
    nlinarith only [first,last,cn.2.2]
  exact ⟨lower,sp,cap,zp,small,cosine,sine⟩

/-- Section 1.1's strict half-angle point follows from the additional
isolated halfpoint exclusion, without any premise about the boundary angle. -/
theorem point (C : OpenSquare) (side : 1<C.side) (cn : Normal C.c C.s)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (A : ¬C.Inside (2/5) 1) (H : ¬C.Inside (1/2) 1)
    (G : ¬C.Inside 1 (13/50)) :
    C.Inside 1 (C1092WallProfileScalars.half C.c C.s) := by
  have data := entrance C side cn M I J O A G
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  have cap : C.loV+C.side≤C.c-C.s/2 := by
    apply le_of_not_gt
    intro high
    apply H
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [M.1,J.2.2.1,high,data.1,side,data.2.2.2.2.2.2,cb.2.1,
        cp,cn.1,cn.2.1]
  let z := C1092WallProfileScalars.half C.c C.s
  have zp : 0<z := data.2.2.2.1
  have small : z<13/50 := data.2.2.2.2.1
  have ids := half_identities C.c C.s cp cn.2.2
  have angle : z*(1+C.c)=C.s := ids.1
  have unitAngle : C.s*z=1-C.c := ids.2
  have identity : C.c-C.s/2+z-1= -C.s*z*(1-z/2) := by
    linear_combination (1/2)*angle+(1-z/2)*unitAngle
  have strict := mul_pos (mul_pos data.2.1 zp)
    (show 0<1-z/2 by linarith only [small])
  have upperU : C.c+C.s*z=1 := by linarith only [unitAngle]
  have upperV : -C.s+C.c*z= -z := by nlinarith only [angle]
  change C.Inside 1 z
  refine ⟨?_,?_,?_,?_⟩
  · nlinarith only [I.1,upperU,cb.2.2.2.1]
  · nlinarith only [upperU,data.1,side]
  · nlinarith only [upperV,identity,strict,cap,side]
  · nlinarith only [upperV,I.2.2.2,zp,cp]

/-- A genuine foreign strict bar, once it has been established, supplies
the quantitative southeast angle bounds of the cited completed prose.
This theorem leaves establishment of that actual bar as an explicit input. -/
theorem small_angle_of_bar (C : OpenSquare) (side : 1<C.side) (cn : Normal C.c C.s)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (O : ¬C.Inside 0 0)
    (A : ¬C.Inside (2/5) 1)
    (bar : ∀ y : ℝ, 0≤y → y≤2/5 → ¬C.Inside 1 y) :
    C.s+(2/5)*C.c<3/5 ∧ C.s<21/100 ∧ 97/100<C.c := by
  have data := entrance C side cn M I J O A
    (bar (13/50) (by norm_num) (by norm_num))
  have cb := normal_bounds cn
  have cp : 0<C.c := by linarith only [cb.1]
  let z := C1092WallProfileScalars.half C.c C.s
  have zp : 0<z := data.2.2.2.1
  have small : z<13/50 := data.2.2.2.2.1
  have ids := half_identities C.c C.s cp cn.2.2
  have angle : z*(1+C.c)=C.s := ids.1
  have unitAngle : C.s*z=1-C.c := ids.2
  have cut : C.s+(2/5)*C.c<3/5 := by
    apply lt_of_not_ge
    intro high
    have identity : C.c-(2/5)*C.s+z-1=z*(3/5-C.s-(2/5)*C.c) := by
      nlinarith only [angle,unitAngle]
    have nonpositive := mul_nonpos_of_nonneg_of_nonpos zp.le
      (show 3/5-C.s-(2/5)*C.c≤0 by linarith only [high])
    have u : C.c+C.s*z=1 := by linarith only [unitAngle]
    have v : -C.s+C.c*z= -z := by nlinarith only [angle]
    apply bar z zp.le (by linarith only [small])
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [I.1,u,cb.2.2.2.1]
    · nlinarith only [u,data.1,side]
    · nlinarith only [v,identity,nonpositive,data.2.2.1,side]
    · nlinarith only [v,I.2.2.2,zp,cp]
  have sine : C.s<21/100 := by
    apply lt_of_not_ge
    intro bad
    have chord := mul_nonneg (show 0≤C.s-21/100 by linarith only [bad])
      (show 0≤3/5-C.s by linarith only [cut,cp])
    have square := mul_pos
      (show 0<3/2-(5/2)*C.s-C.c by linarith only [cut])
      (show 0<3/2-(5/2)*C.s+C.c by linarith only [cut,cp])
    nlinarith only [chord,square,cn.2.2,bad]
  have cosine : 97/100<C.c := by
    have first := mul_pos (show 0<21/100-C.s by linarith only [sine])
      (show 0<21/100+C.s by linarith only [cn.1])
    apply lt_of_not_ge
    intro bad
    have last := mul_nonneg (show 0≤97/100-C.c by linarith only [bad])
      (show 0≤97/100+C.c by linarith only [cp])
    nlinarith only [first,last,cn.2.2]
  exact ⟨cut,sine,cosine⟩

#print axioms entrance
#print axioms point
#print axioms small_angle_of_bar
end N12Compact.C1092MMMPPositiveInwardHalfangle
