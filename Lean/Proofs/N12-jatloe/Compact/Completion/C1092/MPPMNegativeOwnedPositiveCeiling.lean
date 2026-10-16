import Compact.Completion.C1092.MPPMNegativeOwnedPositiveCeilingScalars
import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareGeometry
import Compact.Completion.C1092.TwoFifthsSupport

/-! Complete raw NEGATIVE-OWNED-POSITIVE-CEILING Theorem 1.
W is the actual negative predecessor in the present physical chart.
Its leftmost vertex clearance is a simultaneous face premise, produced
from its genuine wall segment by the original-owner adapter. -/
namespace N12Compact.C1092MPPMNegativeOwnedPositiveCeiling
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
  close : 87/100<W.c
  marker : C.Inside (-7/20) (-7/20)
  ordinary : C.Inside (-1) (-13/50)
  forward : C.Inside (-13/50) 0
  lowerV : (2/5)*C.s-C.c≤C.loV
  predecessorMarker : W.Inside (-7/20) (7/20)
  upperV : W.loV+W.side≤W.c
  upperU : W.loU+W.side≤(7/20)*(W.c+W.s)
  clearance : -1<W.c*W.loU-W.s*W.loV
  apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)

private theorem axes (C W : OpenSquare) (h : Input C W) :
    C.loU+C.side≤lower W C.c C.s ∨
      C.loV+C.side≤lower W (-C.s) C.c ∨
      upper C (-W.s) W.c≤W.loV := by
  have cb := normal_bounds h.sourceNormal
  have wb := normal_bounds h.predecessorNormal
  have cp : 0<C.c := by linarith only [cb.1]
  have bp : 0<W.c := by linarith only [h.close]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower W nx ny) : 0<ny ∧ 0<(13/20)*nx+(61/100)*ny := by
    have marker := (strict_bounds C _ _ nx ny unit h.marker).2
    have ordinary := (strict_bounds C _ _ nx ny unit h.ordinary).2
    have target := (strict_bounds W _ _ nx ny unit h.predecessorMarker).1
    constructor <;> linarith only [marker,ordinary,target,sep]
  rcases C1092MPPMSteepPositiveThreeSquare.signed_axes C W h.same h.apart
      with cu | cu' | cv | cv' | wu | wu' | wv | wv'
  · exact Or.inl (by simpa only [(ownU C).2] using cu)
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) cu').1
    exact False.elim (by linarith only [no,h.positive])
  · exact Or.inr (Or.inl (by simpa only [(ownV C).2] using cv))
  · have no := (cone _ _ (by nlinarith only [C.unit_normal]) cv').1
    exact False.elim (by linarith only [no,cp])
  · have no := (cone _ _ (by nlinarith only [W.unit_normal]) wu).1
    exact False.elim (by linarith only [no,h.predecessorNormal.1])
  · have no := (cone _ _ (by nlinarith only [W.unit_normal]) wu').2
    exact False.elim (by linarith only [no,h.predecessorNormal.2.1,bp])
  · exact Or.inr (Or.inr (by simpa only [(ownV W).1] using wv))
  · have no := (cone _ _ (by nlinarith only [W.unit_normal]) wv').1
    exact False.elim (by linarith only [no,bp])

theorem half_lt (C W : OpenSquare) (h : Input C W) : C.s/(1+C.c)<11/100 := by
  let c := C.c
  let s := C.s
  let b := W.c
  let r := -W.s
  let k := c*b-s*r
  let ell := c*r+s*b
  have cn : Normal c s := h.sourceNormal
  have wn : Normal b r := h.predecessorNormal
  have cb := normal_bounds cn
  have wb := normal_bounds wn
  have cp : 0<c := by linarith only [cb.1]
  have sp : 0<s := h.positive
  have bp : 0<b := by dsimp [b]; linarith only [h.close]
  have rh : r<1/2 := by
    have bSquare := mul_pos (show 0<b-87/100 by dsimp [b]; linarith only [h.close])
      (show 0<b+87/100 by linarith only [bp])
    by_contra no
    have rSquare := mul_nonneg (show 0≤r-1/2 by linarith only [no])
      (show 0≤r+1/2 by linarith only [wn.1])
    nlinarith only [wn.2.2,bSquare,rSquare]
  have kp : 0<k := by
    have first := mul_pos cp (show 0<b-r by dsimp [b] at *; linarith only [h.close,rh])
    have last := mul_nonneg (sub_nonneg.mpr cn.2.1) wn.1
    dsimp [k]
    nlinarith only [first,last]
  have ep : 0<ell := by
    have first := mul_pos sp bp
    have last := mul_nonneg cp.le wn.1
    dsimp [ell]
    nlinarith only [first,last]
  have sumPositive : 0<k+ell := add_pos kp ep
  have upperU : W.loU+C.side≤(7/20)*(b-r) := by
    dsimp [b,r]
    linarith only [h.upperU,h.same]
  have upperV : W.loV+C.side≤b := by
    dsimp [b]
    linarith only [h.upperV,h.same]
  have forwardU : -(13/50)*c<C.loU+C.side := by
    dsimp [c]
    linarith only [h.forward.2.1]
  have forwardV : (13/50)*s<C.loV+C.side := by
    dsimp [s]
    linarith only [h.forward.2.2.2]
  by_contra no
  have large : 11/100≤s/(1+c) := by exact le_of_not_gt no
  rcases axes C W h with own | transverse | target
  · have formula := lower_nn W C.c C.s k ell
      (by dsimp [k,c,s,b,r]; ring) (by dsimp [ell,c,s,b,r]; ring) kp.le ep.le
    have first := mul_le_mul_of_nonneg_left upperU kp.le
    have last := mul_le_mul_of_nonneg_left upperV ep.le
    have margin := Scalars.own_margin cn wn h.close
    have identity : k+ell-(13/50)*c-(7/20)*k*(b-r)-ell*b=
        c*Scalars.P0 b r+s*Scalars.Q0 b r := by
      dsimp [k,ell,Scalars.P0,Scalars.Q0]
      ring
    have side := mul_nonneg (sub_nonneg.mpr h.side.le) sumPositive.le
    nlinarith only [own,formula,first,last,margin,identity,side,forwardU]
  · have formula := lower_np W (-C.s) C.c (-ell) k
      (by dsimp [ell,c,s,b,r]; ring) (by dsimp [k,c,s,b,r]; ring)
      (neg_nonpos.mpr ep.le) kp.le
    rw [←h.same] at formula
    have clear : -1<b*W.loU+r*W.loV := by
      dsimp [b,r]
      linarith only [h.clearance]
    have first := mul_lt_mul_of_pos_left clear ep
    have last := mul_le_mul_of_nonneg_left upperV cp.le
    have side := mul_pos (sub_pos.mpr h.side)
      (show 0<c+ell*b by positivity)
    have identity : b*(-ell*(W.loU+C.side)+k*W.loV)=
        -ell*(b*W.loU+r*W.loV)+c*W.loV-ell*b*C.side := by
      dsimp [k,ell]
      linear_combination (c*W.loV)*wn.2.2
    have comparison : b*lower W (-C.s) C.c<(1-b)*(ell-c) := by
      rw [formula]
      nlinarith only [first,last,side,identity]
    have short := mul_nonneg (show 0≤1-b by linarith only [wb.2.1])
      (mul_nonneg cp.le (show 0≤1-r by linarith only [rh]))
    have gap := mul_pos (show 0<b-87/100 by dsimp [b]; linarith only [h.close])
      (mul_pos sp bp)
    have bound : (1-b)*(ell-c)<(13/100)*s*b := by
      dsimp [ell] at *
      nlinarith only [short,gap]
    have separation := mul_le_mul_of_nonneg_left transverse bp.le
    have strict := mul_lt_mul_of_pos_left forwardV bp
    have positive := mul_pos sp bp
    nlinarith only [comparison,bound,separation,strict,positive]
  · have formula := C1092TwoFifths.Support.upper_pos_pos C (-W.s) W.c ell k
      (by dsimp [ell,c,s,b,r]; ring) (by dsimp [k,c,s,b,r]; ring) ep.le kp.le
    have first := mul_lt_mul_of_pos_left forwardU ep
    have last := mul_le_mul_of_nonneg_left h.lowerV kp.le
    have margin := Scalars.last_margin cn wn large
    have identity : 1+k-b-(13/50)*ell*c+k*((2/5)*s-c)=
        1-Scalars.P1 c s*b-Scalars.Q1 c s*r := by
      dsimp [k,ell,Scalars.P1,Scalars.Q1]
      linear_combination -(13/50)*r*cn.2.2
    have side := mul_nonneg (sub_nonneg.mpr h.side.le)
      (show 0≤1+k by linarith only [kp])
    nlinarith only [target,formula,first,last,margin,identity,side,upperV]

end
end N12Compact.C1092MPPMNegativeOwnedPositiveCeiling
