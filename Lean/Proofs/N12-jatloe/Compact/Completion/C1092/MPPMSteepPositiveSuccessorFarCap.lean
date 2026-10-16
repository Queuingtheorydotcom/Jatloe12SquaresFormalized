import Compact.Completion.C1092.MPPMSteepPositiveSuccessorFarCapScalars
import Compact.Completion.C1092.MPPMElbowIsolation

/-! STEEP-POSITIVE-SUCCESSOR-FAR-CAP Theorem 1, with one literal excluded
segment and the simultaneous faces of the same two actual squares. The
whole-bar threshold argument retains equality, hence vertex tangency.
The half-angle calculation is replaced by its direct linear consequence.
Source only: no compiler or replay has been run. -/
namespace N12Compact.C1092MPPMSteepPositiveSuccessorFarCap
open S12 S12Pilot C977CornerCubic ABTransverse C1092WholeSupports
open C1092MMMPEndingAxes C1092TwoFifths.Support
open C1092MPPMPositiveRetainingSteep.Scalars Scalars
set_option Elab.async false

structure Input (C E : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=E.side
  central : Normal C.c C.s
  steep : 3/5≤C.s
  recipient : Normal E.c E.s
  markerC : C.Inside (-7/20) (-7/20)
  markerE : E.Inside (7/20) (-7/20)
  bottomE : E.Inside (2/5) (-1)
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤0
  lowerV : (14/25)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤(543/500)*C.s
  recipientUpperV : E.loV+E.side≤0
  bar : ∀ y, -(14/25)≤y → y≤-(2/5) → ¬E.Inside 1 y
  apart : ∀ x y,¬(C.Inside x y ∧ E.Inside x y)

/-- The other two bands are strict everywhere on the actual excluded
segment, using the bottom auxiliary and the actual southeast marker. -/
private theorem bar_bands (C E : OpenSquare) (h : Input C E)
    (y : ℝ) (low : -(14/25)≤y) (high : y≤-(2/5)) :
    E.loU<E.c+E.s*y ∧ -E.s+E.c*y<E.loV+E.side := by
  have eb := normal_bounds h.recipient
  have first := mul_nonneg h.recipient.1 (show 0≤y+14/25 by linarith only [low])
  have last := mul_nonneg (show 0≤E.c by linarith only [eb.1])
    (show 0≤-(2/5)-y by linarith only [high])
  constructor <;>
    nlinarith only [first,last,h.bottomE.1,h.markerE.2.2.2,eb.1,h.recipient.1]

private theorem near_cap (C E : OpenSquare) (h : Input C E) :
    E.loU+E.side≤E.c-(2/5)*E.s := by
  have bands := bar_bands C E h (-(2/5)) (by norm_num) (by norm_num)
  apply le_of_not_gt
  intro high
  apply h.bar (-(2/5)) (by norm_num) (by norm_num)
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [bands.1,bands.2,high,h.bottomE.2.2.1,h.recipient.2.1]

/-- If the lower endpoint is not upper-u, the two exit thresholds must
overlap. A strict gap would give an interior point on this very segment. -/
private theorem bar_vertex (C E : OpenSquare) (h : Input C E)
    (_failed : E.c-(14/25)*E.s<E.loU+E.side)
    (low : -E.s-(14/25)*E.c≤E.loV) (tp : 0<E.s) :
    E.c*(E.loU+E.side)-E.s*E.loV≤1 := by
  have eb := normal_bounds h.recipient
  have dp : 0<E.c := by linarith only [eb.1]
  have near := near_cap C E h
  let f := (E.loV+E.s)/E.c
  let u := (E.loU+E.side-E.c)/E.s
  have feq : E.c*f=E.loV+E.s := by dsimp [f]; field_simp [ne_of_gt dp]
  have ueq : E.s*u=E.loU+E.side-E.c := by dsimp [u]; field_simp [ne_of_gt tp]
  have fl : -(14/25)≤f := by
    have scaled : 0≤E.c*(f+14/25) := by nlinarith only [feq,low]
    have sign := nonneg_of_mul_nonneg_right scaled dp
    linarith only [sign]
  have uh : u≤-(2/5) := by
    have scaled : 0≤E.s*(-(2/5)-u) := by nlinarith only [ueq,near]
    have sign := nonneg_of_mul_nonneg_right scaled tp
    linarith only [sign]
  apply le_of_not_gt
  intro gap
  have identity : E.c*E.s*(u-f)=E.c*(E.loU+E.side)-E.s*E.loV-1 := by
    linear_combination E.c*ueq-E.s*feq-h.recipient.2.2
  have order : f<u := by
    have scaled : 0<E.c*E.s*(u-f) := by linarith only [identity,gap]
    have sign := pos_of_mul_pos_right scaled (mul_pos dp tp).le
    linarith only [sign]
  let y := (f+u)/2
  have yl : -(14/25)≤y := by dsimp [y]; linarith only [fl,order]
  have yh : y≤-(2/5) := by dsimp [y]; linarith only [uh,order]
  have fy : 0<E.c*(y-f) := mul_pos dp (by dsimp [y]; linarith only [order])
  have yu : 0<E.s*(u-y) := mul_pos tp (by dsimp [y]; linarith only [order])
  have bands := bar_bands C E h y yl yh
  apply h.bar y yl yh
  refine ⟨by simpa only [mul_one] using bands.1,?_,?_,
    by simpa only [mul_one] using bands.2⟩ <;> nlinarith only [feq,ueq,fy,yu]

private theorem competing_faces (C E : OpenSquare) (h : Input C E)
    (failed : E.c-(14/25)*E.s<E.loU+E.side) :
    E.loU< -(11/25) ∧ -(13/125)<E.loV+E.side ∧ E.loV< -1 ∧
      0<E.loU+E.side := by
  have eb := normal_bounds h.recipient
  have dp : 0<E.c := by linarith only [eb.1]
  have side : 1<E.side := by simpa only [h.same] using h.side
  have bands := bar_bands C E h (-(14/25)) (by norm_num) (by norm_num)
  have low : -E.s-(14/25)*E.c≤E.loV := by
    apply le_of_not_gt
    intro below
    apply h.bar (-(14/25)) (by norm_num) (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bands.1,bands.2,failed,below]
  have width : 1<E.s+(14/25)*E.c := by
    linarith only [low,side,h.recipientUpperV]
  have tp : 0<E.s := by linarith only [width,eb.2.1]
  have wall := bar_vertex C E h failed low tp
  have upperWeight := mul_nonpos_of_nonneg_of_nonpos h.recipient.1 h.recipientUpperV
  have sideWeight := mul_pos (sub_pos.mpr side)
    (show 0<E.c+E.s by linarith only [dp,h.recipient.1])
  have lowerU : E.loU< -(11/25) := by
    have scaled : E.c*(E.loU+11/25)<0 := by
      nlinarith only [wall,upperWeight,sideWeight,width]
    have sign := neg_of_mul_neg_right scaled dp.le
    linarith only [sign]
  have maxWidth := wall_width h.recipient
  refine ⟨lowerU,?_,?_,?_⟩ <;>
    linarith only [low,maxWidth,side,h.recipientUpperV,h.markerE.2.1,h.recipient.2.1]

/-- Every actual-square separating source fails in the competing exit.
The split is on the closed relative frame order, with no angular gap. -/
private theorem competing_impossible (C E : OpenSquare) (h : Input C E)
    (failed : E.c-(14/25)*E.s<E.loU+E.side) : False := by
  have cf := central_bounds h.central h.steep h.side h.lowerU h.lowerV h.upperV
  have ef := competing_faces C E h failed
  have cb := normal_bounds h.central
  have eb := normal_bounds h.recipient
  have cp : 0<C.c := by linarith only [cb.1]
  have sp : 0<C.s := by linarith only [h.steep]
  have dp : 0<E.c := by linarith only [eb.1]
  let k := kappa C.c C.s E.c E.s
  let z := sigma C.c C.s E.c E.s
  have rel := relative_bounds h.central h.recipient
  have kp : 0<k := by dsimp [k]; linarith only [rel.1]
  have kh : k≤1 := rel.2.1
  have lowC : C.loU<0 := by linarith only [h.upperU,h.side]
  have lowV : C.loV<0 := by linarith only [cf.2.2.2]
  have highV : 0<C.loV+C.side := by linarith only [cf.2.1]
  have aWeight := mul_lt_mul_of_pos_left cf.1 kp
  have vWeight := mul_lt_mul_of_pos_left cf.2.2.2 kp
  have eWeight := mul_lt_mul_of_pos_left ef.1 kp
  have dWeight := mul_lt_mul_of_pos_left ef.2.1 kp
  have ownC : upper C C.s (-C.c)= -C.loV := by
    simpa only [neg_neg,(ownV C).1] using upper_neg C (-C.s) C.c
  have ownE : lower E E.s (-E.c)= -(E.loV+E.side) := by
    simpa only [neg_neg,(ownV E).2] using lower_neg E (-E.s) E.c
  have axes := C1092MPPMElbowIsolation.positive_axes C E h.same cp sp dp
    h.recipient.1 h.markerC h.markerE h.apart
  by_cases order : 0≤z
  · have close := close_order h.central h.recipient h.steep order
    have zk : 49/50<k := close.1
    have zh : z<3/20 := close.2
    have az := mul_le_mul_of_nonneg_left cf.1.le order
    have vz := mul_nonneg order highV.le
    have jz := mul_nonneg order ef.2.2.2.le
    have dz := mul_le_mul_of_nonneg_left ef.2.1.le order
    rcases axes with current|transverse|recipient|transverse
    · have formula := lower_pn E C.c C.s k (-z)
        (by dsimp [k,kappa]) (by dsimp [z,sigma]; ring)
        kp.le (by linarith only [order])
      nlinarith only [formula,current,eWeight,dz,cf.1,zk,zh]
    · have formula := (formulas E C.s (-C.c)).1
      have du : C.s*E.c+(-C.c)*E.s= -z := by dsimp [z,sigma]; ring
      have dv : -C.s*E.s+(-C.c)*E.c= -k := by dsimp [k,kappa]; ring
      rw [du,dv,min_eq_left (by linarith only [order]),min_eq_left (by linarith only [kp])] at formula
      rw [ownC] at transverse
      nlinarith only [formula,transverse,jz,dWeight,kh,cf.2.2.2]
    · have formula := upper_nn C E.c E.s k z
        (by dsimp [k,kappa]; ring) (by dsimp [z,sigma]; ring) kp.le order
      nlinarith only [formula,recipient,aWeight,vz,kh,ef.1]
    · have formula := C1092MPPMElbowIsolation.upper_pn C E.s (-E.c) z (-k)
        (by dsimp [z,sigma]; ring) (by dsimp [k,kappa]; ring)
        order (by linarith only [kp])
      rw [ownE] at transverse
      nlinarith only [formula,transverse,az,vWeight,zk,zh,ef.2.1]
  · have order : z≤0 := (lt_of_not_ge order).le
    have weight := earlier_weight h.central h.recipient order
    have qz := mul_le_mul_of_nonneg_left ef.2.2.1.le (neg_nonneg.mpr order)
    have vz := mul_nonneg_of_nonpos_of_nonpos order lowV.le
    have uz := mul_nonneg_of_nonpos_of_nonpos order lowC.le
    have lz := mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr order)
      (show E.loU≤0 by linarith only [ef.1])
    rcases axes with current|transverse|recipient|transverse
    · have formula := lower_nn E C.c C.s k (-z)
        (by dsimp [k,kappa]) (by dsimp [z,sigma]; ring)
        kp.le (neg_nonneg.mpr order)
      nlinarith only [formula,current,eWeight,qz,weight,cf.1]
    · have formula := lower_pn E C.s (-C.c) (-z) (-k)
        (by dsimp [z,sigma]; ring) (by dsimp [k,kappa]; ring)
        (neg_nonneg.mpr order) (by linarith only [kp])
      rw [ownC] at transverse
      nlinarith only [formula,transverse,lz,dWeight,kh,cf.2.2.2]
    · have formula := C1092MPPMElbowIsolation.upper_pn C E.c E.s k z
        (by dsimp [k,kappa]; ring) (by dsimp [z,sigma]; ring) kp.le order
      nlinarith only [formula,recipient,aWeight,vz,kh,ef.1]
    · have formula := C1092MPPMElbowIsolation.upper_nonpositive C E.s (-E.c) z (-k)
        (by dsimp [z,sigma]; ring) (by dsimp [k,kappa]; ring)
        order (by linarith only [kp])
      rw [ownE] at transverse
      have kl : 7/10<k := rel.1
      nlinarith only [formula,transverse,uz,vWeight,kl,ef.2.1]

/-- The actual far segment forces the stronger successor face; no
crosspoint, additional wall, or successor forward point is assumed. -/
theorem upper_cap (C E : OpenSquare) (h : Input C E) :
    E.loU+E.side≤E.c-(14/25)*E.s := by
  apply le_of_not_gt
  intro failed
  exact competing_impossible C E h failed

#print axioms upper_cap
end N12Compact.C1092MPPMSteepPositiveSuccessorFarCap
