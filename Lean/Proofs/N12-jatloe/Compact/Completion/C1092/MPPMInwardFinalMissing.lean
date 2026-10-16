import Compact.Completion.C1092.MPPMInwardFinalMissingScalars
import Compact.Completion.C1092.MPPMInwardFinalCentered
import Compact.Completion.C1092.MMMP.UpperThirdScalars

/-! The actual predecessor comparison and final successor join in
OPPOSED-MISSING-INWARD §§2--6. Every foreign segment below belongs to
the named actual owner; the raw entrance is not a family assertion. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

structure MissingPredecessor (C W : OpenSquare) : Prop where
  same : C.side=W.side
  normal : Normal W.c (-W.s)
  marker : W.Inside (-7/20) (7/20)
  lowerU : -W.c+W.s≤W.loU
  lowerV : (2/5)*W.c+W.s≤W.loV
  upperV : W.loV+W.side≤W.c
  apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)

theorem missing_small (C W : OpenSquare) (h : MissingProfile C)
    (w : MissingPredecessor C W)
    (floor : C.c-1-C.s*(1-C.c-(13/50)*C.s)<C.c*(C.loV+C.side)) :
    half C.c (-C.s)<1/10 := by
  have near := missing_near_center C h floor
  have cb := normal_bounds h.normal
  have wb := normal_bounds w.normal
  have cp : 0<C.c := by linarith only [h.close]
  have wp : 0<W.c := by linarith only [wb.1]
  have angle := predecessor_angle w.normal
    (show 1< -W.s+(3/5)*W.c by linarith only [w.lowerV,w.upperV,w.same,h.side])
  let k := C.c*W.c+C.s*W.s
  let delta := C.s*W.c-C.c*W.s
  have relative := C1092MMMPUpperThirdScalars.relative_bounds h.normal w.normal
  have kp : 7/10<k := by dsimp [k]; nlinarith only [relative.1]
  have choices := upward_axes C W w.same cp h.negative.le wp
    (by linarith only [w.normal.1]) h.marker w.marker w.apart
  have own : C.loV+C.side≤lower W (-C.s) C.c := by
    rcases choices with cu|cv|wu|wv
    · have first := (strict_bounds C _ _ (-C.c) (-C.s)
        (by nlinarith only [C.unit_normal]) h.outer).2
      have last := (strict_bounds W _ _ (-C.c) (-C.s)
        (by nlinarith only [C.unit_normal]) w.marker).1
      exact False.elim (by linarith only [first,last,cu,h.close,h.small])
    · exact cv
    · have first := (strict_bounds C _ _ (-W.c) (-W.s)
        (by nlinarith only [W.unit_normal]) h.outer).2
      exact False.elim (by linarith only [first,wu,w.lowerU,w.same,h.side,w.normal.2.1,wb.2.2.2.2.2])
    · have first := (strict_bounds C _ _ (-W.s) W.c
        (by nlinarith only [W.unit_normal]) near.2).2
      exact False.elim (by linarith only [first,wv,w.upperV,w.same,h.side,angle.2.1,wb.2.2.2.2.2])
  apply lt_of_not_ge
  intro low
  by_cases order : delta≤0
  · have formula := lower_nn W (-C.s) C.c (-delta) k
      (by dsimp [delta]; ring) (by dsimp [k]; ring)
      (by linarith only [order]) (by linarith only [kp])
    have Pneg : W.loU<0 := by linarith only [w.marker.1,wp,w.normal.1]
    have first := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤-delta by linarith only [order]) Pneg.le
    have last := mul_nonneg (show 0≤k by linarith only [kp])
      (show 0≤-2/17-W.loV by linarith only [w.upperV,w.same,h.side,angle.2.1])
    nlinarith only [own,formula,first,last,kp,near.1]
  · have dp : 0<delta := lt_of_not_ge order
    have formula := lower_np W (-C.s) C.c (-delta) k
      (by dsimp [delta]; ring) (by dsimp [k]; ring)
      (by linarith only [dp]) (by linarith only [kp])
    have first := mul_nonneg dp.le
      (show 0≤W.loU+W.c-W.s by linarith only [w.lowerU])
    have last := mul_nonneg (show 0≤k by linarith only [kp])
      (show 0≤W.c-C.side-W.loV by linarith only [w.upperV,w.same])
    have strict := mul_pos (sub_pos.mpr h.side)
      (show 0<delta+k by linarith only [dp,kp])
    have bound : C.loV+C.side<delta*(W.c-W.s-1)+k*(W.c-1) := by
      rw [←w.same] at formula
      nlinarith only [own,formula,first,last,strict]
    have identity : delta*(W.c-W.s-1)+k*(W.c-1)=
        C.c*f W.c (-W.s)+C.s*g W.c (-W.s) := by
      dsimp [delta,k,f,g]
      linear_combination (C.c/2)*W.unit_normal
    rw [identity] at bound
    have scaled := mul_lt_mul_of_pos_left bound cp
    have margin := missing_predecessor_margin h.normal w.normal h.close h.small low angle.2.2.le
    nlinarith only [scaled,margin,floor]

theorem missing_impossible (C W E B R : OpenSquare) (h : MissingProfile C)
    (w : MissingPredecessor C W) (same : C.side=E.side) (e : NegativeSuccessor E)
    (bottomBar : ∀ x : ℝ,-14/25≤x → x≤0 → B.Inside x (-1))
    (rightBar : ∀ y : ℝ,-36/85≤y → y≤0 → R.Inside 1 y)
    (apartCB : ∀ x y,¬(C.Inside x y ∧ B.Inside x y))
    (apartCE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y))
    (apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y))
    (apartEB : ∀ x y,¬(E.Inside x y ∧ B.Inside x y)) : False := by
  have floor := missing_floor C B h bottomBar apartCB
  have small := missing_small C W h w floor
  have far : ¬E.Inside 1 (-36/85) := fun own =>
    apartER _ _ ⟨own,rightBar _ le_rfl (by norm_num)⟩
  have omitted : ¬E.Inside 0 (-1) := fun own =>
    apartEB _ _ ⟨own,bottomBar 0 (by norm_num) le_rfl⟩
  have side : 1<E.side := by simpa only [←same] using h.side
  have cap := successor_far E side e far
  have angle := successor_bottom E side e cap.1 omitted
  have endpoint : Normal (4165/4813) (2412/4813) := by norm_num [Normal]
  have endpointHalf : half (4165/4813) (2412/4813)=(18:ℝ)/67 := by norm_num [half]
  have cross := half_cross endpoint e.normal (by simpa only [endpointHalf] using angle.2.le)
  have margins := missing_final_margins h.normal e.normal small.le cross
  have order := relative_order h.normal e.normal
    (show half C.c (-C.s)<half E.c (-E.s) by linarith only [small,angle.2])
  exact successor_impossible C E (13/50) 0 h.side same h.normal e h.marker h.inner
    (by linarith only [h.lowerU]) h.upperV cap.1 (by nlinarith only [order])
    margins.1 margins.2 apartCE

#print axioms missing_small
#print axioms missing_impossible
end N12Compact.C1092MPPMInwardFinal
