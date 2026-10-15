import Compact.Completion.C1092.MPPMInwardFinalCapScalars
import Compact.Completion.C1092.MPPMInwardFinalPredecessor
import Compact.Completion.C1092.MMMP.UpperThirdScalars

/-! The actual predecessor normal joins in CENTERED-NEGATIVE-INWARD-H-CAP.
No opposite-owner type, wall origin, or predecessor sign is assumed. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092TwoFifths.Support C1092WallProfileScalars
set_option Elab.async false

structure CenteredCapInput (C W : OpenSquare) : Prop where
  side : 1<C.side
  same : C.side=W.side
  normal : Normal C.c (-C.s)
  center : C.Inside 0 0
  marker : C.Inside (-7/20) (-7/20)
  upperA : C.loU+C.side≤(7/20)*(C.c-C.s)
  upperH : C.loV+C.side≤(7/20)*(C.c+C.s)
  firstCap : C.loU+C.side≤(7/50)*C.c-C.s/2
  previous : PredecessorPoints W
  apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)

theorem reject_first (C W : OpenSquare) (h : CenteredCapInput C W)
    (sep : upper C (-C.c) (-C.s)≤lower W (-C.c) (-C.s)) : False := by
  have cb := normal_bounds h.normal
  have formula : upper C (-C.c) (-C.s)= -C.loU := by rw [upper_neg,(ownU C).1]
  have mark := (strict_bounds W _ _ (-C.c) (-C.s)
    (by nlinarith only [C.unit_normal]) h.previous.marker).1
  rw [formula] at sep
  linarith only [sep,mark,h.upperA,h.side,cb.2.2.2.2.2]

theorem positive_axes (C W : OpenSquare) (h : CenteredCapInput C W)
    (wn : Normal W.c W.s) :
    C.loV+C.side≤lower W (-C.s) C.c ∨ upper C (-W.s) W.c≤W.loV := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [cb.1]
  have wp : 0<W.c := by linarith only [wb.1]
  have upward (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower W nx ny) : 0<ny := by
    have first := (strict_bounds C _ _ nx ny unit h.marker).2
    have last := (strict_bounds W _ _ nx ny unit h.previous.marker).1
    linarith only [first,last,sep]
  have axes := CongruentSAT.faceSeparation_of_disjoint C W h.same h.apart
  change pairRadius C W≤|C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W≤|-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C≤|W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C≤|-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius C nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [eq])
  rcases axes with cu|cv|wu|wv
  · rcases split _ _ _ (parallel_radius C W) cu with direct|back
    · have no := upward C.c C.s C.unit_normal direct
      exact False.elim (by linarith only [no,h.normal.1])
    · exact False.elim (reject_first C W h (reverse C W _ _ back))
  · rcases split _ _ _ (transverse_radius C W) cv with direct|back
    · exact Or.inl (by simpa only [(ownV C).2] using direct)
    · have no := upward C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using reverse C W _ _ back)
      exact False.elim (by linarith only [no,cp])
  · have radius : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]; exact parallel_radius W C
    rcases split _ _ _ radius wu with direct|back
    · have first := (strict_bounds C _ _ W.c W.s W.unit_normal h.center).2
      have last := (strict_bounds W _ _ W.c W.s W.unit_normal h.previous.marker).1
      exact False.elim (by linarith only [first,last,direct,wn.2.1])
    · have no := upward (-W.c) (-W.s) (by nlinarith only [W.unit_normal]) (reverse C W _ _ back)
      exact False.elim (by linarith only [no,wn.1])
  · have radius : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]; exact transverse_radius W C
    rcases split _ _ _ radius wv with direct|back
    · exact Or.inr (by simpa only [(ownV W).1] using direct)
    · have no := upward W.s (-W.c) (by nlinarith only [W.unit_normal])
        (by simpa only [neg_neg] using reverse C W _ _ back)
      exact False.elim (by linarith only [no,wp])

private theorem positive_height (C W : OpenSquare) (h : CenteredCapInput C W)
    (wn : Normal W.c W.s) : C.loV+C.side<17/125 := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [cb.1]
  have wp : 0<W.c := by linarith only [wb.1]
  have table := nonnegative_predecessor_faces W (by simpa only [←h.same] using h.side) wn h.previous
  let k := C.c*W.c+C.s*W.s
  let j := C.c*W.s-C.s*W.c
  have kn : 0≤k := by
    have first := mul_nonneg (show 0≤C.c+C.s by linarith only [h.normal.2.1]) wp.le
    have last := mul_nonneg h.normal.1 (sub_nonneg.mpr wn.2.1)
    dsimp [k]; nlinarith only [first,last]
  have jn : 0≤j := by
    have first := mul_nonneg cp.le wn.1
    have last := mul_nonneg h.normal.1 wp.le
    dsimp [j]; nlinarith only [first,last]
  have sum : 0<j+k := by
    have first := mul_pos (show 0<C.c-C.s by linarith only [cp,h.normal.1]) wp
    have last := mul_nonneg (show 0≤C.c+C.s by linarith only [h.normal.2.1]) wn.1
    dsimp [j,k]; nlinarith only [first,last]
  have unit : k^2+j^2=1 := by
    calc
      _ = (C.c^2+C.s^2)*(W.c^2+W.s^2) := by dsimp [k,j]; ring
      _ = 1 := by rw [C.unit_normal,W.unit_normal]; norm_num
  have ku : k≤1 := by nlinarith only [unit,sq_nonneg j,sq_nonneg (k-1)]
  apply lt_of_not_ge
  intro high
  rcases positive_axes C W h wn with own|last
  · have formula := lower_nn W (-C.s) C.c j k
      (by dsimp [j]; ring) (by dsimp [k]; ring) jn kn
    rcases table.2 with topV|topU
    · have Pneg : W.loU≤0 := by linarith only [h.previous.marker.1,wn.2.1]
      have first := mul_nonpos_of_nonneg_of_nonpos jn Pneg
      have second := mul_nonneg kn
        (show 0≤43/500-W.loV by linarith only [topV,h.side,h.same,wb.2.1])
      nlinarith only [own,formula,first,second,ku,high]
    · have first := mul_nonneg jn
        (show 0≤(543/500)*W.s-C.side-W.loU by linarith only [topU.1,h.same])
      have strict := mul_pos (sub_pos.mpr h.side) sum
      rcases topU.2 with upper|lower
      · have second := mul_nonneg kn
          (show 0≤W.c+W.s-C.side-W.loV by linarith only [upper,h.same])
        have bound : C.loV+C.side<j*((543/500)*W.s-1)+k*(W.c+W.s-1) := by
          nlinarith only [own,formula,first,second,strict]
        have identity : j*((543/500)*W.s-1)+k*(W.c+W.s-1)=
            C.c*((W.c+W.s-1)^2/2+(43/500)*W.s^2)+
              C.s*(W.s^2+W.c-W.s-(43/500)*W.c*W.s) := by
          dsimp [j,k]
          linear_combination (C.c/2)*W.unit_normal
        have margins := cap_f0 wn
        have one := mul_lt_mul_of_pos_left margins.1 cp
        have two := mul_nonpos_of_nonpos_of_nonneg
          (show C.s≤0 by linarith only [h.normal.1]) margins.2
        rw [identity] at bound
        nlinarith only [bound,one,two,cb.2.1,high]
      · have second := mul_nonneg kn
          (show 0≤(543/500)*W.c+W.s-C.side-W.loV by linarith only [table.1,h.same])
        have bound : C.loV+C.side<j*((543/500)*W.s-1)+k*((543/500)*W.c+W.s-1) := by
          nlinarith only [own,formula,first,second,strict]
        have identity : j*((543/500)*W.s-1)+k*((543/500)*W.c+W.s-1)=
            C.c*(43/500+(W.c+W.s-1)^2/2)+C.s*(W.s^2+W.c-W.s) := by
          dsimp [j,k]
          linear_combination ((293/500)*C.c)*W.unit_normal
        have margins := cap_g0 wn lower.2.2
        have one := mul_lt_mul_of_pos_left margins.1 cp
        have two := mul_nonpos_of_nonpos_of_nonneg
          (show C.s≤0 by linarith only [h.normal.1]) margins.2
        rw [identity] at bound
        nlinarith only [bound,one,two,cb.2.1,high]
  · have formula := upper_np C (-W.s) W.c (-j) k
      (by dsimp [j]; ring) (by dsimp [k]; ring) (by linarith only [jn]) kn
    have first := mul_nonneg jn
      (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.firstCap])
    have second := mul_nonneg kn
      (show 0≤C.loV+C.side-17/125 by linarith only [high])
    have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+j by linarith only [jn])
    have margin := cap_own_positive h.normal wn
    dsimp [centeredD,j,k] at formula first second strict margin
    nlinarith only [last,formula,first,second,strict,margin,table.1,h.same]

private theorem nonpositive_height (C W : OpenSquare) (h : CenteredCapInput C W)
    (wn : Normal W.c (-W.s)) : C.loV+C.side<17/125 := by
  have cb := normal_bounds h.normal
  have wb := normal_bounds wn
  have cp : 0<C.c := by linarith only [cb.1]
  have wp : 0<W.c := by linarith only [wb.1]
  have table := nonpositive_predecessor_faces W (by simpa only [←h.same] using h.side) wn h.previous
  let k := C.c*W.c+C.s*W.s
  let delta := C.s*W.c-C.c*W.s
  have relative := C1092MMMPUpperThirdScalars.relative_bounds h.normal wn
  have kp : 7/10<k := by dsimp [k]; nlinarith only [relative.1]
  have ku : k≤1 := by dsimp [k]; nlinarith only [relative.2.2.1]
  have Ap : 0<C.loU+C.side := by linarith only [h.center.2.1]
  have Aback : 0< -C.loU := by linarith only [h.center.1]
  have Hp : 0<C.loV+C.side := by linarith only [h.center.2.2.2]
  apply lt_of_not_ge
  intro high
  rcases upward_axes C W h.same cp (by linarith only [h.normal.1]) wp
      (by linarith only [wn.1]) h.marker h.previous.marker h.apart with first|own|wu|wv
  · exact reject_first C W h first
  · by_cases order : delta≤0
    · have formula := lower_nn W (-C.s) C.c (-delta) k
        (by dsimp [delta]; ring) (by dsimp [k]; ring)
        (by linarith only [order]) (by linarith only [kp])
      have Pneg : W.loU≤0 := by linarith only [h.previous.marker.1,wp,wn.1]
      have first := mul_nonpos_of_nonneg_of_nonpos (show 0≤-delta by linarith only [order]) Pneg
      have second := mul_nonneg (show 0≤k by linarith only [kp])
        (show 0≤43/500-W.loV by linarith only [table.2,h.side,h.same,wb.2.1])
      nlinarith only [own,formula,first,second,ku,high]
    · have dp : 0<delta := lt_of_not_ge order
      have formula := lower_np W (-C.s) C.c (-delta) k
        (by dsimp [delta]; ring) (by dsimp [k]; ring)
        (by linarith only [dp]) (by linarith only [kp])
      have first := mul_nonneg dp.le (show 0≤W.loU+W.c-W.s by linarith only [table.1])
      have second := mul_nonneg (show 0≤k by linarith only [kp])
        (show 0≤(543/500)*W.c-C.side-W.loV by linarith only [table.2,h.same])
      have strict := mul_pos (sub_pos.mpr h.side) (show 0<delta+k by linarith only [dp,kp])
      have bound : C.loV+C.side<delta*(W.c-W.s-1)+k*((543/500)*W.c-1) := by
        rw [←h.same] at formula
        nlinarith only [own,formula,first,second,strict]
      have identity : delta*(W.c-W.s-1)+k*((543/500)*W.c-1)=
          C.c*((43/500)*W.c^2+f W.c (-W.s))+
            C.s*(g W.c (-W.s)+(43/500)*W.c*W.s) := by
        dsimp [delta,k,f,g]
        linear_combination (C.c/2)*W.unit_normal
      have margins := cap_negative_fg wn
      have one := mul_lt_mul_of_pos_left margins.1 cp
      have two := mul_nonpos_of_nonpos_of_nonneg
        (show C.s≤0 by linarith only [h.normal.1]) margins.2
      rw [identity] at bound
      nlinarith only [bound,one,two,cb.2.1,high]
  · by_cases order : 0≤delta
    · have formula := upper_np C (-W.c) (-W.s) (-k) delta
        (by dsimp [k]; ring) (by dsimp [delta]; ring) (by linarith only [kp]) order
      have first := mul_nonneg (show 0≤k by linarith only [kp])
        (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.firstCap])
      have second := mul_nonneg order (show 0≤C.loV+C.side-17/125 by linarith only [high])
      have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k by linarith only [kp])
      have margin := cap_left_positive h.normal wn
      dsimp [centeredD,k,delta] at formula first second strict margin
      nlinarith only [wu,formula,first,second,strict,margin,table.1,h.same]
    · have formula := upper_neg_neg C (-W.c) (-W.s) (-k) delta
        (by dsimp [k]; ring) (by dsimp [delta]; ring)
        (by linarith only [kp]) (by linarith only [order])
      have first := mul_nonneg (show 0≤k by linarith only [kp])
        (show 0≤(7/50)*C.c-C.s/2-C.loU-C.side by linarith only [h.firstCap])
      have second := mul_nonneg (show 0≤-delta by linarith only [order])
        (show 0≤(7/20)*(C.c+C.s)-C.loV-C.side by linarith only [h.upperH])
      have strict := mul_pos (sub_pos.mpr h.side) (show 0<1+k-delta by linarith only [kp,order])
      have margin := cap_left_before h.normal wn (by dsimp [delta] at order; nlinarith only [order])
      dsimp [centeredD,k,delta] at formula first second strict margin
      nlinarith only [wu,formula,first,second,strict,margin,table.1,h.same]
  · have second := mul_nonneg (show 0≤k by linarith only [kp])
      (show 0≤C.loV+C.side-17/125 by linarith only [high])
    by_cases order : 0≤delta
    · have formula := upper_pos_pos C (-W.s) W.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring) order (by linarith only [kp])
      have first := mul_nonneg order Ap.le
      nlinarith only [wv,formula,first,second,kp,table.2,h.same,h.side,wb.2.1]
    · have formula := upper_np C (-W.s) W.c delta k
        (by dsimp [delta]; ring) (by dsimp [k]; ring)
        (by linarith only [order]) (by linarith only [kp])
      have first := mul_nonneg (show 0≤-delta by linarith only [order]) Aback.le
      nlinarith only [wv,formula,first,second,kp,table.2,h.same,h.side,wb.2.1]

theorem centered_height_cap (C W : OpenSquare) (h : CenteredCapInput C W)
    (canonical : |W.s|≤W.c) : C.loV+C.side<17/125 := by
  by_cases sign : 0≤W.s
  · exact positive_height C W h ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,W.unit_normal⟩
  · have wn : Normal W.c (-W.s) :=
      ⟨by linarith only [sign],by linarith only [(abs_le.mp canonical).1],by nlinarith only [W.unit_normal]⟩
    exact nonpositive_height C W h wn

/-- Both bounds of the cap chapter, with the first-face cap produced
from the actual successor and diagonal point instead of postulated. -/
theorem centered_caps (C E W : OpenSquare) (side : 1<C.side)
    (sameE : C.side=E.side) (sameW : C.side=W.side)
    (cn : Normal C.c (-C.s)) (center : C.Inside 0 0)
    (marker : C.Inside (-7/20) (-7/20))
    (southeast : ¬C.Inside (7/20) (-7/20))
    (northwest : ¬C.Inside (-7/20) (7/20))
    (e : NegativeSuccessor E) (w : PredecessorPoints W) (canonical : |W.s|≤W.c)
    (apartCE : ∀ x y,¬(C.Inside x y ∧ E.Inside x y))
    (apartCW : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) :
    C.loU+C.side≤(7/50)*C.c-C.s/2 ∧ C.loV+C.side<17/125 := by
  have markers := centered_marker_caps C side cn center marker southeast northwest
  have first := centered_first_cap C E side sameE cn center marker southeast northwest e apartCE
  have input : CenteredCapInput C W :=
    ⟨side,sameW,cn,center,marker,markers.1,markers.2,first,w,apartCW⟩
  exact ⟨first,centered_height_cap C W input canonical⟩

#print axioms centered_height_cap
#print axioms centered_caps
end N12Compact.C1092MPPMInwardFinal
