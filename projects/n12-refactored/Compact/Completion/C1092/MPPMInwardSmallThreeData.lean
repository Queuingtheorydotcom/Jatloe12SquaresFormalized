import Compact.Completion.C1092.MPPMInwardSmallThreeScalars
import Compact.Completion.C1092.MPPMInwardFinalSuccessor

/-! The three actual squares in SMALL-INWARD-THREE-SQUARE-ENDING.
The successor profile is explicit here. The original-family adapter
already proves it from the genuine corner marker and right-wall bar
in MPPMActualInwardSuccessor.successor_profile; no finite catalogue or
unwritten weak-input sign certificate is assumed. -/
namespace N12Compact.C1092MPPMInwardSmallThree
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
open C1092MPPMInwardFinal
set_option Elab.async false
noncomputable section

structure Input (C B E : OpenSquare) : Prop where
  bottom : BottomAngle.Input C B
  sameE : C.side=E.side
  successor : NegativeSuccessor E
  apartCE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)
  apartBE : ∀ x y,¬(B.Inside x y ∧ E.Inside x y)

theorem successor_low (C B E : OpenSquare) (h : Input C B E) : 1/3< -E.s := by
  let d := E.c
  let t := -E.s
  have en : Normal d t := h.successor.normal
  have eb := normal_bounds en
  have width : 1<t+(343/500)*d := by
    dsimp [d,t]
    linarith only [h.successor.lowerV,h.successor.upperV,h.bottom.side,h.sameE]
  apply lt_of_not_ge
  intro low
  have cap : d≤1-t^2/2 := by nlinarith only [sq_nonneg (1-d),en.2.2]
  have first := mul_nonneg (show 0≤1/3-t by linarith only [low])
    (show 0≤1-(343/1000)*(t+1/3) by linarith only [low])
  nlinarith only [cap,first,width]

theorem successor_bounds (C B E : OpenSquare) (h : Input C B E) :
    15/17<E.c ∧ -E.s<8/17 := by
  let c := C.c
  let s := -C.s
  let d := E.c
  let t := -E.s
  let k := kappa c s d t
  let e := delta c s d t
  have cn : Normal c s := h.bottom.normal
  have en : Normal d t := h.successor.normal
  have cb := normal_bounds cn
  have eb := normal_bounds en
  have angle := BottomAngle.angle C B h.bottom
  have small : half c s≤53/500 := angle.2.2.le
  have bounds := small_bounds cn small
  have low : 1/3<t := successor_low C B E h
  have cp : 0<c := by linarith only [cb.1]
  have dp : 0<d := by linarith only [eb.1]
  have kp : 0<k := by
    have first := mul_pos cp dp
    have last := mul_nonneg cn.1 en.1
    dsimp [k,kappa]; nlinarith only [first,last]
  have ep : 0<e := by
    have first := mul_pos (show 0<c-97/100 by linarith only [bounds.1])
      (show 0<t by linarith only [low])
    have last := mul_nonneg cn.1 (show 0≤1-d by linarith only [eb.2.1])
    dsimp [e,delta]; nlinarith only [first,last,low,bounds.2]
  have central := BottomAngle.central_faces C B h.bottom
  have high : t<8/17 := by
    apply lt_of_not_ge
    intro large
    have source := first_margin cn en small large
    have target := last_margin cn en small large
    have reserve := mul_pos (sub_pos.mpr h.bottom.side)
      (show 0<1+k+e by linarith only [kp,ep])
    rcases longitudinal_axes C E h.sameE cn en h.bottom.marker h.successor.marker
      h.bottom.inner h.successor.halfpoint h.apartCE with own|foreign
    · have formula := lower_nn E C.c C.s k e
        (by dsimp [k,kappa,c,s,d,t]; ring) (by dsimp [e,delta,c,s,d,t]; ring) kp.le ep.le
      have first := mul_le_mul_of_nonneg_left h.successor.upperU kp.le
      have last := mul_le_mul_of_nonneg_left h.successor.upperV ep.le
      rw [←h.sameE] at first last
      dsimp [FC,Q,kappa,delta,k,e,c,s,d,t] at source reserve formula first last
      nlinarith only [own,formula,first,last,source,reserve,central.lowerU]
    · have formula := upper_pos_neg C E.c E.s k (-e)
        (by dsimp [k,kappa,c,s,d,t]; ring) (by dsimp [e,delta,c,s,d,t]; ring)
        kp.le (neg_nonpos.mpr ep.le)
      have first := mul_le_mul_of_nonneg_left central.lowerU kp.le
      have last := mul_le_mul_of_nonpos_left central.upperV (neg_nonpos.mpr ep.le)
      have upperU : E.loU+C.side≤d+t := by
        dsimp [d,t]; linarith only [h.successor.upperU,h.sameE]
      dsimp [FE,Q,kappa,delta,k,e,c,s,d,t] at target reserve formula first last upperU
      nlinarith only [foreign,formula,first,last,target,reserve,upperU]
  have cosine : 15/17<d := by
    have square := mul_pos (show 0<8/17-t by linarith only [high])
      (show 0<8/17+t by linarith only [en.1])
    nlinarith only [square,en.2.2,eb.1,sq_nonneg (d-15/17)]
  exact ⟨cosine,high⟩

end
end N12Compact.C1092MPPMInwardSmallThree
