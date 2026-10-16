import Compact.Completion.C1092.MPPMMissingPositiveFaces
import Compact.Completion.C1092.ShallowCentralScalars

/-! C1092-MPPM-MISSING-POSITIVE-BOUNDARIES, section 1. The preceding
actual boundary origin improves the old marker cap to K <= s. All four
faces, both widths and the strict half-angle entrance are produced from
literal points. Neither neighboring boundary is assigned an orientation.
Written source only; no compilation is claimed. -/
namespace N12Compact.C1092MPPMMissingPositiveBoundaries
open S12 S12Pilot C977CornerCubic C1092WallProfileScalars
set_option Elab.async false

structure Data (C : OpenSquare) : Prop where
  normal : Normal C.c C.s
  marker : C.Inside (-7/20) (-7/20)
  ordinaryP : C.Inside (-1) (-13/50)
  ordinaryG : C.Inside (-1) (-2/5)
  halfpoint : C.Inside (-1) (-1/2)
  corner : ¬C.Inside (-1) (-1)
  previousOrigin : ¬C.Inside (-1) 0
  forward : ¬C.Inside (-13/50) 0
  farBottom : ¬C.Inside (-14/25) (-1)
  innerBottom : ¬C.Inside (-13/50) (-1)

def Data.of_inputs (C : OpenSquare) (normal : Normal C.c C.s)
    (h : C1092MPPMMissingPositiveFaces.Inputs C)
    (previousOrigin : ¬C.Inside (-1) 0) : Data C where
  normal := normal
  marker := h.marker
  ordinaryP := h.ordinaryP
  ordinaryG := h.ordinaryG
  halfpoint := h.halfpoint
  corner := h.corner
  previousOrigin := previousOrigin
  forward := h.forward
  farBottom := h.farBottom
  innerBottom := h.innerBottom

structure Profile (C : OpenSquare) : Prop where
  lowerU : -C.c-C.s≤C.loU
  upperU : C.loU+C.side≤-(13/50)*C.c
  lowerV : (14/25)*C.s-C.c≤C.loV
  upperV : C.loV+C.side≤C.s
  positive : 0<C.s
  widthU : C.side≤(37/50)*C.c+C.s
  widthV : C.side≤C.c+(11/25)*C.s
  halfLow : 13/87<half C.c C.s
  halfHigh : half C.c C.s<1/2

theorem profile (C : OpenSquare) (side : 1<C.side) (h : Data C) : Profile C := by
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  have upperV : C.loV+C.side≤C.s := by
    apply le_of_not_gt
    intro high
    apply h.previousOrigin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [h.ordinaryP.1,h.marker.2.1,h.ordinaryP.2.2.1,
        high,cp,h.normal.1,h.normal.2.1]
  have lowerU : -C.c-C.s≤C.loU := by
    apply le_of_not_gt
    intro low
    have lowerV : C.s-C.c≤C.loV := by
      apply le_of_not_gt
      intro lowV
      apply h.corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,lowV,h.halfpoint.2.1,h.halfpoint.2.2.2,cp,h.normal.1]
    linarith only [lowerV,upperV,side,cb.2.1]
  have upperU : C.loU+C.side≤-(13/50)*C.c := by
    apply le_of_not_gt
    intro high
    have smallV : C.loV+C.side≤(13/50)*C.s := by
      apply le_of_not_gt
      intro highV
      apply h.forward
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [h.ordinaryP.1,h.marker.2.2.1,high,highV,
          cp,h.normal.1,h.normal.2.1]
    have innerLowU : C.loU< -(13/50)*C.c-C.s := by
      linarith only [h.ordinaryP.1,h.normal.2.1]
    have innerLowV : C.loV<(13/50)*C.s-C.c := by
      linarith only [smallV,side,cb.2.1]
    have innerHighV : (13/50)*C.s-C.c<C.loV+C.side := by
      linarith only [h.ordinaryP.2.2.2,cp,h.normal.1]
    have innerHighU : C.loU+C.side≤-(13/50)*C.c-C.s := by
      apply le_of_not_gt
      intro highU
      apply h.innerBottom
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [innerLowU,highU,innerLowV,innerHighV]
    linarith only [lowerU,innerHighU,side,cb.2.1]
  have shortFar : (3/10)*C.c+C.s<1 := by
    linarith only [cb.2.2.2.2.2,h.normal.2.1]
  have lowerV : (14/25)*C.s-C.c≤C.loV := by
    apply le_of_not_gt
    intro low
    have farHighU : C.loU+C.side≤-(14/25)*C.c-C.s := by
      apply le_of_not_gt
      intro high
      apply h.farBottom
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,upperU,side,shortFar,h.ordinaryP.2.2.2,cp,h.normal.1]
    linarith only [farHighU,lowerU,side,cb.2.1]
  have widthU : C.side≤(37/50)*C.c+C.s := by linarith only [lowerU,upperU]
  have widthV : C.side≤C.c+(11/25)*C.s := by linarith only [lowerV,upperV]
  have sp : 0<C.s := by linarith only [widthU,side,cb.2.1]
  let q := half C.c C.s
  have hh : q<1/2 := by
    dsimp [q,half]
    apply (div_lt_iff₀ (show 0<1+C.c by linarith only [cp])).mpr
    linarith only [cb.2.2.2.2.2,h.normal.2.1,cb.1]
  have hd := quarter_data C.c C.s cp.le h.normal.1 h.normal.2.2
  have identity : (1+q^2)*((37/50)*C.c+C.s-1)=(1-q)*(87*q-13)/50 := by
    linear_combination (37/50)*hd.2.2.2.1+hd.2.2.2.2
  have positive := mul_pos (show 0<1+q^2 by nlinarith only [sq_nonneg q])
    (show 0<(37/50)*C.c+C.s-1 by linarith only [widthU,side])
  rw [identity] at positive
  have low : 13/87<q := by
    by_contra failed
    have bad := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-q by linarith only [hh])
      (show 87*q-13≤0 by linarith only [le_of_not_gt failed])
    linarith only [positive,bad]
  exact ⟨lowerU,upperU,lowerV,upperV,sp,widthU,widthV,low,hh⟩

/-- The deliberately coarse exact bounds in (4), including the true
lower central endpoint rather than a sampled angle interval. -/
theorem central_bounds (C : OpenSquare) (side : 1<C.side) (h : Data C) :
    7/10<C.c ∧ 29/100<C.s ∧ C.s<71/100 ∧ C.c*C.s≤1/2 ∧
      156/125<C.c+C.s ∧ 0≤C.c-C.s ∧ C.c-C.s<133/200 ∧
      (61/200)*C.c<C.s ∧ C.c<3700/3869 ∧ 1131/3869<C.s := by
  have p := profile C side h
  have cb := normal_bounds h.normal
  have cp : 0<C.c := by linarith only [cb.1]
  let q := half C.c C.s
  have qn : 0≤q := (quarter_data C.c C.s cp.le h.normal.1 h.normal.2.2).1
  have low : 13/87<q := p.halfLow
  have high : q<1/2 := p.halfHigh
  have hd := quarter_data C.c C.s cp.le h.normal.1 h.normal.2.2
  have den : 0<1+q^2 := by nlinarith only [sq_nonneg q]
  have cosine : (1+q^2)*(3700/3869-C.c)=2*(q-13/87)*(q+13/87)/(1+(13/87)^2) := by
    linear_combination -hd.2.2.2.1
  have sine : (1+q^2)*(C.s-1131/3869)=2*(q-13/87)*(1-(13/87)*q)/(1+(13/87)^2) := by
    linear_combination hd.2.2.2.2
  have csmall : C.c<3700/3869 := by
    have pos : 0<2*(q-13/87)*(q+13/87)/(1+(13/87)^2) := by positivity
    rw [←cosine] at pos
    exact sub_pos.mp (pos_of_mul_pos_right pos den.le)
  have sbig : 1131/3869<C.s := by
    have last : 0<1-(13/87)*q := by linarith only [high]
    have pos : 0<2*(q-13/87)*(1-(13/87)*q)/(1+(13/87)^2) := by positivity
    rw [←sine] at pos
    exact sub_pos.mp (pos_of_mul_pos_right pos den.le)
  have cross : C.c*C.s≤1/2 := by
    nlinarith only [h.normal.2.2,sq_nonneg (C.c-C.s)]
  have difference := mul_nonneg (sub_nonneg.mpr h.normal.2.1)
    (show 0≤C.c+C.s by linarith only [cp,h.normal.1])
  have cStrict : 7/10<C.c := by
    nlinarith only [h.normal.2.2,difference,cb.1]
  have sSmall : C.s<71/100 := by
    by_contra failed
    have product := mul_nonneg h.normal.1
      (show 0≤C.s-71/100 by linarith only [failed])
    nlinarith only [h.normal.2.2,difference,product,failed]
  have sumLow : 156/125<C.c+C.s := by
    have factor : (1+q^2)*(C.c+C.s-156/125)=
        (-281*q^2+250*q-31)/125 := by
      linear_combination hd.2.2.2.1+hd.2.2.2.2
    have first := mul_nonneg (show 0≤q-13/87 by linarith only [low])
      (show 0≤1/2-q by linarith only [high])
    have positive : 0< -281*q^2+250*q-31 := by nlinarith only [first,low,high]
    have product : 0<(1+q^2)*(C.c+C.s-156/125) := by rw [factor]; linarith only [positive]
    exact sub_pos.mp (pos_of_mul_pos_right product den.le)
  exact ⟨cStrict,by linarith only [sbig],sSmall,cross,
    sumLow,sub_nonneg.mpr h.normal.2.1,
    by linarith only [csmall,sbig],by linarith only [csmall,sbig],csmall,sbig⟩

#print axioms profile
#print axioms central_bounds
end N12Compact.C1092MPPMMissingPositiveBoundaries
