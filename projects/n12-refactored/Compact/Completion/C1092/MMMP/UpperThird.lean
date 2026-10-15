import Compact.Completion.C1092.MMMP.UpperThirdScalars
import Compact.Completion.C1092.MMMP.EndingAxes
import Compact.Completion.C1092.MMMP.TwoFifthsEntranceNortheast

/-! The whole local W--N conclusion of NORTHEAST-UPPER-THIRD §4.
The two upper faces belong to the same actual W and all four northeast
faces belong to the same actual N.  Congruent SAT supplies the alternatives;
no separating support or extra enclosure is an input. -/
namespace N12Compact.C1092MMMPUpperThird
open S12 S12Pilot ABTransverse C977CornerCubic C977CornerSectorBounds
open C1092WholeSupports C1092MMMPEndingAxes C1092MMMPUpperThirdScalars
open C1092MMMPTwoFifthsEntrance
set_option Elab.async false

private theorem sum_cap {b t : ℝ} (bn : Normal b t) : b+t<71/50 := by
  have bb := normal_bounds bn
  apply lt_of_not_ge
  intro high
  have product := mul_nonneg (show 0≤b+t-71/50 by linarith only [high])
    (show 0≤b+t+71/50 by linarith only [bb.1,bn.1])
  nlinarith only [product,bn.2.2,sq_nonneg (b-t)]

theorem upper_third (W N : OpenSquare) (side : 1<W.side) (same : W.side=N.side)
    (dn : Normal W.c W.s) (angle : 8*W.s<7*W.c)
    (origin : W.Inside 0 0) (wm : W.Inside (-7/20) (7/20))
    (height : 23/25<W.loV+W.side)
    (floor : W.side-W.c+(2/5)*W.s≤W.loU+W.side)
    (north : NortheastCore N)
    (apart : ∀ x y, ¬(W.Inside x y ∧ N.Inside x y)) :
    3*N.s<1+N.c := by
  have bn : Normal N.c N.s := ⟨north.sine.le,north.canonical,N.unit_normal⟩
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0<W.c := by linarith only [db.1]
  have bounds := shallow_bounds dn angle
  apply lt_of_not_ge
  intro half
  have steep : 3/5≤N.s := by
    apply le_of_not_gt
    intro small
    have cosine : 4/5≤N.c := cosine_order (by norm_num [Normal]) bn small.le
    linarith only [small,cosine,half]
  have cap := cosine_cap bn steep
  have sum := sum_cap bn
  let d := W.c
  let r := W.s
  let b := N.c
  let t := N.s
  let A := W.loU+W.side
  let H := W.loV+W.side
  let alpha := b*d+t*r
  let beta := t*d-b*r
  have relative := relative_bounds dn bn
  have ap : 0<alpha := by dsimp [alpha,b,t,d,r]; linarith only [relative.1]
  have aOne : alpha≤1 := relative.2.2.1
  have Nlow : N.loU<21/50 := by
    have upper := north.upperU
    rw [←same] at upper
    linarith only [upper,sum,side]
  have NlowNonnegative : 0≤N.loU := by linarith only [north.lowerU,north.sine]
  have Nheight : N.loV<0 := by
    have upper := north.upperV
    rw [←same] at upper
    linarith only [upper,cap,side]
  have Wlow : W.loV<0 := by
    have low := origin.2.2.1
    dsimp [OpenSquare.Inside,InBands] at low
    linarith only [low]
  have axes := C1092MMMPEndingAxes.alternatives W N same dp dn.1 dn.2.1
    north.cosine north.sine.le north.canonical origin wm north.marker apart
  by_cases order : 0≤b*r-t*d
  · let gamma := b*r-t*d
    have gn : 0≤gamma := order
    have sineOrder : N.s≤W.s := sine_order dn bn (by
      dsimp [b,r,t,d] at order
      nlinarith only [order])
    have cosineOrder : W.c≤N.c := cosine_order dn bn sineOrder
    have Alow : 11/25<A := by
      dsimp [A]
      linarith only [floor,side,cosineOrder,cap,sineOrder,steep]
    have gammaCap : gamma≤1/10 := by
      have first := mul_le_mul_of_nonneg_right cap dn.1
      have last := mul_le_mul_of_nonneg_right steep dp.le
      dsimp [gamma,b,r,t,d]
      nlinarith only [first,last,bounds.1,bounds.2]
    have gammaSquare := mul_nonneg (sub_nonneg.mpr gammaCap)
      (show 0≤1/10+gamma by linarith only [gn])
    have unit : alpha^2+gamma^2=1 := by
      dsimp [alpha,gamma,b,t,d,r]
      nlinarith only [relative.2.2.2]
    have alphaHigh : 49/50<alpha := by
      apply lt_of_not_ge
      intro no
      have square := mul_nonneg (show 0≤49/50-alpha by linarith only [no])
        (show 0≤49/50+alpha by linarith only [ap])
      nlinarith only [square,gammaSquare,unit]
    rcases axes with own | neighbor
    · have formula := lower_nn N d r alpha gamma
        (by dsimp [d,r,alpha,b,t]; ring)
        (by dsimp [d,r,gamma,b,t]; ring) ap.le gn
      have first := mul_le_mul_of_nonneg_right aOne NlowNonnegative
      have last := mul_nonpos_of_nonneg_of_nonpos gn Nheight.le
      change A≤lower N d r at own
      nlinarith only [own,formula,first,last,Alow,Nlow]
    · have formula : upper W b t=alpha*A-gamma*W.loV := by
        have du : b*W.c+t*W.s=alpha := by dsimp [b,t,alpha,d,r]; ring
        have dv : -b*W.s+t*W.c= -gamma := by dsimp [b,t,gamma,d,r]; ring
        rw [(formulas W b t).2,du,dv,max_eq_left ap.le,
          max_eq_right (show -gamma≤0 by linarith only [gn])]
        dsimp [A]
        ring
      have first := mul_lt_mul_of_pos_left Alow ap
      have last := mul_nonpos_of_nonneg_of_nonpos gn Wlow.le
      change upper W b t≤N.loU at neighbor
      nlinarith only [neighbor,formula,first,last,alphaHigh,Nlow]
  · have betap : 0<beta := by dsimp [beta]; linarith only [order]
    have lowerFormula := lower_pn N d r alpha (-beta)
      (by dsimp [d,r,alpha,b,t]; ring)
      (by dsimp [d,r,beta,b,t]; ring) ap.le (by linarith only [betap])
    have upperFormula := upper_nn W b t alpha beta
      (by dsimp [d,r,alpha,b,t]; ring)
      (by dsimp [d,r,beta,b,t]; ring) ap.le betap.le
    have upperU : N.loU≤b+t-W.side := by
      have upper := north.upperU
      rw [←same] at upper
      dsimp [b,t]
      linarith only [upper]
    rcases axes with own | neighbor
    · have Wfloor : W.side-d+(39/100)*r≤A := by
        dsimp [d,r,A]
        linarith only [floor,dn.1]
      have lowerV : W.side+(39/100)*b-t≤N.loV+N.side := by
        rw [←same]
        dsimp [b,t]
        linarith only [north.lowerV,north.cosine]
      have first := mul_le_mul_of_nonneg_left upperU ap.le
      have last := mul_le_mul_of_nonneg_left lowerV betap.le
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<1+alpha+beta by linarith only [ap,betap])
      have positive := C1092MMMPFinalScalars39.own_positive dn bn steep
      change A≤lower N d r at own
      dsimp [C1092MMMPFinalScalars39.ownMargin] at positive
      dsimp [alpha,beta,d,r,b,t,A] at first last strict lowerFormula own Wfloor
      nlinarith only [own,lowerFormula,first,last,Wfloor,strict,positive]
    · have first := mul_le_mul_of_nonneg_left floor ap.le
      have last := mul_le_mul_of_nonneg_left height.le betap.le
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<1+alpha by linarith only [ap])
      have positive := neighbor_positive dn bn bounds.1 bounds.2 steep
        (show 0≤N.s*W.c-N.c*W.s by exact betap.le)
      change upper W b t≤N.loU at neighbor
      dsimp [margin] at positive
      dsimp [alpha,beta,d,r,b,t,A,H] at first last strict upperFormula upperU neighbor
      nlinarith only [neighbor,upperFormula,first,last,upperU,strict,positive]

#print axioms upper_third
end N12Compact.C1092MMMPUpperThird
