import Compact.Completion.C1092.MPPMInwardFinalMargins
import Compact.Completion.C1092.TwoFifthsSupport

/-! Both inward endings use these same physical successor faces and
actual square-normal cover. The strict inner point (0,-.26), already
present in both chapters, removes both upward transverse normals. The
far point and bottom origin are explicit omissions from this same E.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

theorem width_half (k : ℝ) {d t : ℝ} (dn : Normal d t) (kn : -1<k)
    (width : 1<t+k*d) : (1-k)/(1+k)<half d t := by
  have db := normal_bounds dn
  have data := quarter_data d t (by linarith only [db.1]) dn.1 dn.2.2
  let z := half d t
  have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
  have identity : (1+z^2)*(t+k*d-1)=(1-z)*((1+k)*z-(1-k)) := by
    linear_combination k*data.2.2.2.1+data.2.2.2.2
  have positive := mul_pos den (sub_pos.mpr width)
  have factor : 0<(1+k)*z-(1-k) := by
    apply lt_of_not_ge
    intro no
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-z by linarith only [data.2.1]) no
    nlinarith only [positive,identity,bad]
  apply (div_lt_iff₀ (by linarith only [kn] : 0<1+k)).mpr
  nlinarith only [factor]

structure NegativeSuccessor (E : OpenSquare) : Prop where
  normal : Normal E.c (-E.s)
  marker : E.Inside (7/20) (-7/20)
  outer : E.Inside (13/50) (-1)
  halfpoint : E.Inside (1/2) (-1)
  lowerU : -(13/50)*E.s≤E.loU
  upperU : E.loU+E.side≤E.c-E.s
  lowerV : -(543/500)*E.c≤E.loV
  upperV : E.loV+E.side≤-E.s-(2/5)*E.c

theorem successor_far (E : OpenSquare) (side : 1<E.side) (h : NegativeSuccessor E)
    (far : ¬E.Inside 1 (-36/85)) :
    E.loV+E.side≤-E.s-(36/85)*E.c ∧
      2869/14131<half E.c (-E.s) := by
  have eb := normal_bounds h.normal
  have ep : 0<E.c := by linarith only [eb.1]
  have angle := width_half (343/500) h.normal (by norm_num)
    (show 1< -E.s+(343/500)*E.c by linarith only [h.lowerV,h.upperV,side])
  norm_num at angle
  let z := half E.c (-E.s)
  have data := quarter_data E.c (-E.s) ep.le h.normal.1 h.normal.2.2
  have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
  have narrowIdentity : (1+z^2)*(E.c-(139/850)*E.s-1)=2*z*(139/850-z) := by
    nlinarith only [data.2.2.2.1,data.2.2.2.2]
  have narrow : E.c-(139/850)*E.s≤1 := by
    have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*z by linarith only [data.1])
      (show 139/850-z≤0 by linarith only [angle])
    apply le_of_not_gt
    intro no
    have positive := mul_pos den (sub_pos.mpr no)
    nlinarith only [positive,narrowIdentity,bad]
  have upperU : E.c-(36/85)*E.s<E.loU+E.side := by
    apply lt_of_not_ge
    intro cap
    linarith only [cap,h.lowerU,side,narrow]
  have cap : E.loV+E.side≤-E.s-(36/85)*E.c := by
    apply le_of_not_gt
    intro high
    apply far
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.marker.1,h.outer.2.2.1,high,upperU,ep,h.normal.1]
  have finalAngle := width_half (5631/8500) h.normal (by norm_num)
    (show 1< -E.s+(5631/8500)*E.c by linarith only [h.lowerV,cap,side])
  exact ⟨cap,by norm_num at finalAngle; exact finalAngle⟩

theorem successor_bottom (E : OpenSquare) (side : 1<E.side) (h : NegativeSuccessor E)
    (cap : E.loV+E.side≤-E.s-(36/85)*E.c)
    (bottom : ¬E.Inside 0 (-1)) :
    -E.c≤E.loV ∧ 18/67<half E.c (-E.s) := by
  have eb := normal_bounds h.normal
  have ep : 0<E.c := by linarith only [eb.1]
  have negative : E.s<0 := by
    have width : 1< -E.s+(343/500)*E.c := by linarith only [h.lowerV,h.upperV,side]
    linarith only [width,eb.2.1,h.normal.1]
  have lowU : E.loU< -E.s := by linarith only [h.upperU,side,eb.2.1]
  have floor : -E.c≤E.loV := by
    apply le_of_not_gt
    intro low
    apply bottom
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.outer.2.1,h.outer.2.2.2,lowU,low,ep,negative]
  have angle := width_half (49/85) h.normal (by norm_num)
    (show 1< -E.s+(49/85)*E.c by linarith only [floor,cap,side])
  exact ⟨floor,by norm_num at angle; exact angle⟩

theorem longitudinal_axes (C E : OpenSquare) (same : C.side=E.side)
    (cn : Normal C.c (-C.s)) (en : Normal E.c (-E.s))
    (M : C.Inside (-7/20) (-7/20)) (N : E.Inside (7/20) (-7/20))
    (I : C.Inside 0 (-13/50)) (Y : E.Inside (1/2) (-1))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) :
    C.loU+C.side≤lower E C.c C.s ∨ upper C E.c E.s≤E.loU := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have ep : 0<E.c := by linarith only [(normal_bounds en).1]
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
  have downward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower E nx ny) : 0<(1/2)*nx-(37/50)*ny := by
    have first := (strict_bounds C _ _ nx ny unit I).2
    have last := (strict_bounds E _ _ nx ny unit Y).1
    linarith only [first,last,sep]
  rcases choices with cu|cv|eu|ev
  · rcases split _ _ _ (parallel_radius C E) cu with direct|back
    · exact Or.inl (by simpa only [(ownU C).2] using direct)
    · have no := rightward (-C.c) (-C.s) (by nlinarith only [C.unit_normal]) (reverse C E _ _ back)
      exact False.elim (by linarith only [no,cp])
  · rcases split _ _ _ (transverse_radius C E) cv with direct|back
    · have no := downward (-C.s) C.c (by nlinarith only [C.unit_normal]) direct
      exact False.elim (by linarith only [no,cn.2.1,cp])
    · have no := rightward C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using reverse C E _ _ back)
      exact False.elim (by linarith only [no,cn.1])
  · have radius : supportRadius C E.c E.s+supportRadius E E.c E.s=pairRadius E C := by
      rw [add_comm]; exact parallel_radius E C
    rcases split _ _ _ radius eu with direct|back
    · exact Or.inr (by simpa only [(ownU E).1] using direct)
    · have no := rightward (-E.c) (-E.s) (by nlinarith only [E.unit_normal]) (reverse C E _ _ back)
      exact False.elim (by linarith only [no,ep])
  · have radius : supportRadius C (-E.s) E.c+supportRadius E (-E.s) E.c=pairRadius E C := by
      rw [add_comm]; exact transverse_radius E C
    rcases split _ _ _ radius ev with direct|back
    · have no := downward (-E.s) E.c (by nlinarith only [E.unit_normal]) direct
      exact False.elim (by linarith only [no,en.2.1,ep])
    · have no := rightward E.s (-E.c) (by nlinarith only [E.unit_normal])
        (by simpa only [neg_neg] using reverse C E _ _ back)
      exact False.elim (by linarith only [no,en.1])

theorem successor_impossible (C E : OpenSquare) (beta H : ℝ)
    (side : 1<C.side) (same : C.side=E.side)
    (cn : Normal C.c (-C.s)) (en : NegativeSuccessor E)
    (M : C.Inside (-7/20) (-7/20)) (I : C.Inside 0 (-13/50))
    (lowerA : C.side-C.c-beta*C.s≤C.loU+C.side)
    (height : C.loV+C.side≤H)
    (cap : E.loV+E.side≤-E.s-(36/85)*E.c)
    (order : 0<C.s*E.c-C.c*E.s)
    (firstMargin : 0<FC beta C.c (-C.s) E.c (-E.s))
    (lastMargin : 0<FE beta H C.c (-C.s) E.c (-E.s))
    (apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)) : False := by
  let k := C.c*E.c+C.s*E.s
  let delta := C.s*E.c-C.c*E.s
  have kp : 0<k := by
    have first := mul_pos (show 0<C.c by linarith only [(normal_bounds cn).1])
      (show 0<E.c by linarith only [(normal_bounds en.normal).1])
    have last := mul_nonneg cn.1 en.normal.1
    dsimp [k]
    nlinarith only [first,last]
  have dp : 0<delta := order
  have strict := mul_pos (sub_pos.mpr side) (show 0<1+k+delta by linarith only [kp,dp])
  have choices := longitudinal_axes C E same cn en.normal M en.marker I en.halfpoint apart
  rcases choices with own|neighbor
  · have formula := lower_nn E C.c C.s k delta
      (by dsimp [k]) (by dsimp [delta]; ring) kp.le dp.le
    have first := mul_nonneg kp.le
      (show 0≤E.c-E.s-C.side-E.loU by linarith only [en.upperU,same])
    have last := mul_nonneg dp.le
      (show 0≤-E.s-(36/85)*E.c-C.side-E.loV by linarith only [cap,same])
    dsimp [FC,alpha,k,delta] at firstMargin strict formula first last
    nlinarith only [own,formula,first,last,strict,lowerA,firstMargin]
  · have formula := upper_pos_neg C E.c E.s k (-delta)
      (by dsimp [k]; ring) (by dsimp [delta]; ring) kp.le (by linarith only [dp])
    have first := mul_nonneg kp.le
      (show 0≤C.loU+C.c+beta*C.s by linarith only [lowerA])
    have last := mul_nonneg dp.le
      (show 0≤H-C.side-C.loV by linarith only [height])
    dsimp [FE,alpha,k,delta] at lastMargin strict formula first last
    nlinarith only [neighbor,formula,first,last,strict,lastMargin,en.upperU,same]

#print axioms successor_far
#print axioms successor_bottom
#print axioms successor_impossible
end N12Compact.C1092MPPMInwardFinal
