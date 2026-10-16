import Compact.Completion.C1092.MPPMNegativeMissingPositiveCeilingScalars
import Compact.Completion.C1092.MPPMNegativeOwnedPositiveCeiling

/-! The genuine missing-negative predecessor cap gives the closed-arc
7/24 ceiling for a positive forward owner. Every support below belongs
to the same two actual squares; all eight directed SAT candidates are
retained before the strict marker cone removes the impossible ones. -/
namespace N12Compact.C1092MPPMNegativeMissingPositiveCeiling
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092WholeSupports
set_option Elab.async false
noncomputable section

structure Input (C W : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=W.side
  sourceNormal : Normal C.c C.s
  positive : 0<C.s
  predecessorNormal : Normal W.c (-W.s)
  cosineHigh : W.c<33/40
  sineLow : 283/500< -W.s
  product : 23/50<W.c*(-W.s)
  marker : C.Inside (-7/20) (-7/20)
  ordinary : C.Inside (-1) (-13/50)
  forward : C.Inside (-13/50) 0
  lowerV : (2/5)*C.s-C.c≤C.loV
  predecessorMarker : W.Inside (-7/20) (7/20)
  lowerU : -W.c+W.s≤W.loU
  upperU : W.loU+W.side≤(13/50)*W.s
  upperV : W.loV+W.side≤(543/500)*W.c
  apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)

private theorem axes (C W : OpenSquare) (h : Input C W) :
    C.loU+C.side≤lower W C.c C.s ∨
      C.loV+C.side≤lower W (-C.s) C.c ∨
      upper C (-W.s) W.c≤W.loV := by
  have cp : 0<C.c := by linarith only [(normal_bounds h.sourceNormal).1]
  have bp : 0<W.c := by linarith only [(normal_bounds h.predecessorNormal).1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower W nx ny) : 0<ny ∧ 0<(13/20)*nx+(61/100)*ny := by
    have first := (strict_bounds C _ _ nx ny unit h.marker).2
    have second := (strict_bounds C _ _ nx ny unit h.ordinary).2
    have target := (strict_bounds W _ _ nx ny unit h.predecessorMarker).1
    constructor <;> linarith only [first,second,target,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes C W h.same h.apart
      with cu | cu' | cv | cv' | wu | wu' | wv | wv'
  · exact Or.inl (by simpa only [(ownU C).2] using cu)
  · have bad := (cone _ _ (by nlinarith only [C.unit_normal]) cu').1
    exact False.elim (by linarith only [bad,h.positive])
  · exact Or.inr (Or.inl (by simpa only [(ownV C).2] using cv))
  · have bad := (cone _ _ (by nlinarith only [C.unit_normal]) cv').1
    exact False.elim (by linarith only [bad,cp])
  · have bad := (cone _ _ (by nlinarith only [W.unit_normal]) wu).1
    exact False.elim (by linarith only [bad,h.predecessorNormal.1])
  · have bad := (cone _ _ (by nlinarith only [W.unit_normal]) wu').2
    exact False.elim (by linarith only [bad,h.predecessorNormal.2.1,bp])
  · exact Or.inr (Or.inr (by simpa only [(ownV W).1] using wv))
  · have bad := (cone _ _ (by nlinarith only [W.unit_normal]) wv').1
    exact False.elim (by linarith only [bad,bp])

theorem half_lt (C W : OpenSquare) (h : Input C W) : C.s/(1+C.c)<7/24 := by
  let c := C.c
  let s := C.s
  let b := W.c
  let r := -W.s
  let k := c*b-s*r
  let ell := c*r+s*b
  have cn : Normal c s := h.sourceNormal
  have wn : Normal b r := h.predecessorNormal
  have cp : 0<c := by linarith only [(normal_bounds cn).1]
  have bp : 0<b := by linarith only [(normal_bounds wn).1]
  have sp : 0<s := h.positive
  have kn : 0≤k := by
    have first := mul_nonneg (sub_nonneg.mpr cn.2.1) bp.le
    have last := mul_nonneg cn.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]
    nlinarith only [first,last]
  have ep : 0<ell := by
    have first := mul_pos sp bp
    have last := mul_nonneg cp.le wn.1
    dsimp [ell]
    nlinarith only [first,last]
  have sumPositive : 0<k+ell := by linarith only [kn,ep]
  have upperU : W.loU+C.side≤-(13/50)*r := by
    dsimp [r]
    linarith only [h.upperU,h.same]
  have upperV : W.loV+C.side≤(543/500)*b := by
    dsimp [b]
    linarith only [h.upperV,h.same]
  have rounded : W.loV+C.side≤(11/10)*b := by
    linarith only [upperV,bp]
  have forwardU : -(13/50)*c<C.loU+C.side := by
    dsimp [c]
    linarith only [h.forward.2.1]
  by_contra no
  have large : 7/24≤s/(1+c) := le_of_not_gt no
  rcases axes C W h with own | transverse | target
  · have formula := lower_nn W C.c C.s k ell
      (by dsimp [k,c,s,b,r]; ring) (by dsimp [ell,c,s,b,r]; ring) kn ep.le
    have first := mul_le_mul_of_nonneg_left upperU kn
    have last := mul_le_mul_of_nonneg_left rounded ep.le
    have margin := Scalars.own_margin cn wn h.cosineHigh h.sineLow
    have identity : k+ell-(13/50)*c+(13/50)*k*r-(11/10)*ell*b=
        c*Scalars.P0 b r+s*Scalars.Q0 b r := by
      dsimp [k,ell,Scalars.P0,Scalars.Q0]
      ring
    have side := mul_nonneg (sub_nonneg.mpr h.side.le) sumPositive.le
    nlinarith only [own,formula,first,last,margin,identity,side,forwardU]
  · have formula := lower_np W (-C.s) C.c (-ell) k
      (by dsimp [ell,c,s,b,r]; ring) (by dsimp [k,c,s,b,r]; ring)
      (neg_nonpos.mpr ep.le) kn
    rw [←h.same] at formula
    have lowerU : -b-r≤W.loU := by simpa only [b,r,sub_neg_eq_add] using h.lowerU
    have first := mul_le_mul_of_nonpos_left lowerU (neg_nonpos.mpr ep.le)
    have last := mul_le_mul_of_nonneg_left upperV kn
    have side := mul_pos (sub_pos.mpr h.side) sumPositive
    have identity : ell*(b+r)+(543/500)*k*b-k-ell=
        c*Scalars.f2 b r+s*Scalars.g2 b r := by
      dsimp [k,ell,Scalars.f2,Scalars.g2]
      linear_combination c*wn.2.2
    have bound := Scalars.coefficient_bounds wn h.cosineHigh h.product
    have fbound := mul_lt_mul_of_pos_left bound.1 cp
    have gbound := mul_lt_mul_of_pos_left bound.2 sp
    have margin := Scalars.transverse_margin cn large
    nlinarith only [transverse,formula,first,last,side,identity,fbound,gbound,
      h.lowerV,h.side,margin]
  · have formula := C1092TwoFifths.Support.upper_pos_pos C (-W.s) W.c ell k
      (by dsimp [ell,c,s,b,r]; ring) (by dsimp [k,c,s,b,r]; ring) ep.le kn
    have first := mul_lt_mul_of_pos_left forwardU ep
    have last := mul_le_mul_of_nonneg_left h.lowerV kn
    have margin := Scalars.last_margin cn wn large
    have identity : 1+k-(11/10)*b-(13/50)*ell*c+k*((2/5)*s-c)=
        1-Scalars.P1 c s*b-Scalars.Q1 c s*r := by
      dsimp [k,ell,Scalars.P1,Scalars.Q1]
      linear_combination -(13/50)*r*cn.2.2
    have side := mul_nonneg (sub_nonneg.mpr h.side.le) (show 0≤1+k by linarith only [kn])
    nlinarith only [target,formula,first,last,margin,identity,side,rounded]

end
#print axioms half_lt
end N12Compact.C1092MPPMNegativeMissingPositiveCeiling
