import Compact.Completion.C1092.MPPMElbowIsolationScalars
import Compact.Completion.C1092.ElbowProfile
import Compact.Completion.C1092.MMMP.EndingAxes
import Compact.Completion.C1092.TwoFifthsSupport

/-! NONORDINARY-ISOLATION Theorem 2 on the actual two squares.
D is recorded before the simultaneous quarter turn: its physical image
is `clockwise D`. No square is moved independently inside the packing. -/
namespace N12Compact.C1092MPPMElbowIsolation
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
open C1092MMMPEndingAxes C1092TwoFifths.Support C1092MPPMElbowScalars
open C977ChainBridge ThreeSquare
set_option Elab.async false

theorem upper_pn (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : 0≤d) (en : e≤0) : upper Q nx ny=d*(Q.loU+Q.side)+e*Q.loV := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_left dn,max_eq_right en]
  ring

theorem upper_nonpositive (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : d≤0) (en : e≤0) : upper Q nx ny=d*Q.loU+e*Q.loV := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_right dn,max_eq_right en]
  ring

/-- Strict markers orient every actual separating normal rightward.
The zero successor tilt is included in this exhaustive four-source list. -/
theorem positive_axes (C E : OpenSquare) (same : C.side=E.side)
    (cp : 0<C.c) (sp : 0<C.s) (dp : 0<E.c) (tn : 0≤E.s)
    (M : C.Inside (-7/20) (-7/20)) (N : E.Inside (7/20) (-7/20))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    C.loU+C.side≤lower E C.c C.s ∨
      upper C C.s (-C.c)≤lower E C.s (-C.c) ∨
      upper C E.c E.s≤E.loU ∨ upper C E.s (-E.c)≤lower E E.s (-E.c) := by
  have choices := CongruentSAT.faceSeparation_of_disjoint C E same apart
  change pairRadius C E≤|C.c*(centerX E-centerX C)+C.s*(centerY E-centerY C)| ∨
    pairRadius C E≤|-C.s*(centerX E-centerX C)+C.c*(centerY E-centerY C)| ∨
    pairRadius E C≤|E.c*(centerX E-centerX C)+E.s*(centerY E-centerY C)| ∨
    pairRadius E C≤|-E.s*(centerX E-centerX C)+E.c*(centerY E-centerY C)| at choices
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius E nx ny=radius)
      (sep : radius≤|nx*(centerX E-centerX C)+ny*(centerY E-centerY C)|) :=
    separated C E nx ny (by rwa [eq])
  have rightward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<nx := by
    have first := (strict_bounds C _ _ nx ny unit M).2
    have last := (strict_bounds E _ _ nx ny unit N).1
    linarith only [first,last,sep]
  rcases choices with cu|cv|eu|ev
  · rcases split _ _ _ (parallel_radius C E) cu with direct|back
    · exact Or.inl (by simpa only [(ownU C).2] using direct)
    · have no := rightward (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (reverse C E _ _ back)
      exact False.elim (by linarith only [no,cp])
  · rcases split _ _ _ (transverse_radius C E) cv with direct|back
    · have no := rightward (-C.s) C.c (by nlinarith only [C.unit_normal]) direct
      exact False.elim (by linarith only [no,sp])
    · right; left
      simpa only [neg_neg] using reverse C E _ _ back
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]; exact parallel_radius E C
    rcases split _ _ _ radius eu with direct|back
    · right; right; left
      simpa only [(ownU E).1] using direct
    · have no := rightward (-E.c) (-E.s) (by nlinarith only [E.unit_normal])
        (reverse C E _ _ back)
      exact False.elim (by linarith only [no,dp])
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]; exact transverse_radius E C
    rcases split _ _ _ radius ev with direct|back
    · have no := rightward (-E.s) E.c (by nlinarith only [E.unit_normal]) direct
      exact False.elim (by linarith only [no,tn])
    · right; right; right
      simpa only [neg_neg] using reverse C E _ _ back

theorem impossible (C D : OpenSquare) (side : 1<C.side) (same : C.side=D.side)
    (h : C1092ElbowProfile.Profile C) (g : C1092ElbowProfile.Profile D)
    (M : C.Inside (-7/20) (-7/20)) (N : D.Inside (-7/20) (-7/20))
    (Q : D.Inside (-13/50) 0)
    (apart : ∀ x y,¬(C.Inside x y ∧ D.Inside y (-x))) : False := by
  let E := clockwise D
  have marker : E.Inside (7/20) (-7/20) := by
    apply (inside_clockwise _ _ _).mpr
    convert N using 1 <;> norm_num
  have point : E.Inside 0 (-13/50) := by
    apply (inside_clockwise _ _ _).mpr
    simpa only [neg_zero] using Q
  have disjoint : ∀ x y,¬(C.Inside x y ∧ E.Inside x y) := fun x y both =>
    apart x y ⟨both.1,(inside_clockwise _ _ _).mp both.2⟩
  have cp : 0<C.c := by linarith only [h.cosine]
  have dp : 0<E.c := by dsimp [E,clockwise]; linarith only [g.cosine]
  have en : Normal E.c E.s := g.normal
  have common : C.side=E.side := same
  let k := kappa C.c C.s E.c E.s
  let l := sigma C.c C.s E.c E.s
  have rel := frames h.normal en
  have kp : 0<k := by dsimp [k]; linarith only [rel.1]
  have low : E.loU≤E.c-(2/5)*E.s-C.side := by
    dsimp [E,clockwise]
    linarith only [g.lowerV,same]
  have transverseLow : -E.c-(2/5)*E.s≤E.loV := g.lowerU
  have transverseHigh : E.loV≤-(13/50)*E.s-C.side := by
    dsimp [E,clockwise]
    linarith only [g.upperU,same]
  have firstFloor : C.side-C.c-(2/5)*C.s≤C.loU+C.side := by
    linarith only [h.lowerU]
  have lastFloor : C.side+(2/5)*C.s-C.c≤C.loV+C.side := by
    linarith only [h.lowerV]
  have lastCap : C.loV≤(7/20)*(C.c+C.s)-C.side := by linarith only [h.upperV]
  have transverseBlocked (nx ny : ℝ) (unit : nx^2+ny^2=1) (negative : ny<0)
      (sep : upper C nx ny≤lower E nx ny) : False := by
    have first := (strict_bounds C _ _ nx ny unit h.crosspoint).2
    have last := (strict_bounds E _ _ nx ny unit point).1
    nlinarith only [first,last,negative,sep]
  have axes := positive_axes C E common cp h.sinePositive dp g.normal.1 M marker disjoint
  rcases axes with own|cross|neighbor|cross
  · by_cases order : 0≤l
    · have formula := lower_pn E C.c C.s k (-l)
        (by dsimp [k,kappa]) (by dsimp [l,sigma]; ring) kp.le (by linarith only [order])
      have first := mul_le_mul_of_nonneg_left low kp.le
      have last := mul_le_mul_of_nonneg_left transverseLow order
      rw [←common] at formula
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k+l by linarith only [kp,order])
      have margin := first_nonnegative h.normal en order
      dsimp [F0,k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [own,formula,first,last,strict,margin,firstFloor]
    · have ln : l≤0 := (lt_of_not_ge order).le
      have formula := lower_nn E C.c C.s k (-l)
        (by dsimp [k,kappa]) (by dsimp [l,sigma]; ring) kp.le (by linarith only [ln])
      have first := mul_le_mul_of_nonneg_left low kp.le
      have last := mul_le_mul_of_nonneg_left transverseHigh (show 0≤-l by linarith only [ln])
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k-l by linarith only [kp,ln])
      have margin := third_nonnegative h.normal en ln
      dsimp [F2,k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [own,formula,first,last,strict,margin,firstFloor]
  · exact transverseBlocked C.s (-C.c) (by nlinarith only [C.unit_normal])
      (by linarith only [cp]) cross
  · by_cases order : 0≤l
    · have formula := upper_nn C E.c E.s k l
        (by dsimp [k,kappa]; ring) (by dsimp [l,sigma]; ring) kp.le order
      have first := mul_le_mul_of_nonneg_left firstFloor kp.le
      have last := mul_le_mul_of_nonneg_left lastFloor order
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k+l by linarith only [kp,order])
      have margin := second_nonnegative h.normal en order
      dsimp [F1,k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [neighbor,formula,first,last,strict,margin,low]
    · have ln : l≤0 := (lt_of_not_ge order).le
      have formula := upper_pn C E.c E.s k l
        (by dsimp [k,kappa]; ring) (by dsimp [l,sigma]; ring) kp.le ln
      have first := mul_le_mul_of_nonneg_left firstFloor kp.le
      have last := mul_le_mul_of_nonpos_left lastCap ln
      have strict := mul_pos (sub_pos.mpr side) (show 0<1+k-l by linarith only [kp,ln])
      have margin := fourth_nonnegative h.normal en h.sine.le ln
      dsimp [F3,k,l,kappa,sigma] at formula first last strict margin
      nlinarith only [neighbor,formula,first,last,strict,margin,low]
  · exact transverseBlocked E.s (-E.c) (by nlinarith only [E.unit_normal])
      (by linarith only [dp]) cross

#print axioms impossible
end N12Compact.C1092MPPMElbowIsolation
