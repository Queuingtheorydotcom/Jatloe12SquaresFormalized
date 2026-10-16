import Compact.Completion.OtherCases.PositiveEndingWalls
import Compact.Completion.OtherCases.SupportBands

/-! Full support comparisons for every surviving face normal of the
positive southeast ending. Both actual bottom-bar alternatives and both
relative orders of the two physical squares are retained. -/
namespace N12Compact.Completion.OtherCases.PositiveEndingSupports
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

private theorem floor_upper (E : OpenSquare) (data : PositiveEndingFaces.Data E)
    (floor : -1≤E.s*E.loU+E.c*E.loV) : -(12/113)<E.loV+E.side := by
  have first := mul_nonneg data.sinePositive.le (sub_nonneg.mpr data.upperU)
  have last := mul_nonneg data.sinePositive.le (sub_nonneg.mpr data.cosineUpper)
  have extra := mul_pos (sub_pos.mpr data.sideLarge)
    (show 0<E.c+E.s by linarith only [data.cosineLarge,data.sinePositive])
  have scaled : 0<E.c*(E.loV+E.side+12/113) := by
    nlinarith only [floor,first,last,extra,data.cosineLarge]
  have positive := (mul_pos_iff_of_pos_left
    (show 0<E.c by linarith only [data.cosineLarge])).mp scaled
  linarith only [positive]

theorem own_axis (W E : OpenSquare) (data : PositiveEndingFaces.Data E)
    (west : W.Inside (-7/20) (-7/20))
    (sep : upper W E.s (-E.c)≤lower E E.s (-E.c)) : False := by
  have unit : E.s^2+(-E.c)^2=1 := by nlinarith only [E.unit_normal]
  have strict := (strict_bounds W _ _ E.s (-E.c) unit west).2
  have own : lower E E.s (-E.c)= -(E.loV+E.side) := by
    have h := WallProfile.lower_neg E (-E.s) E.c
    simpa only [neg_neg,(ownV E).2] using h
  rw [own] at sep
  rcases data.bar with face | floor
  · have cap := InwardSignScalars.projection_cap E.c E.s
      (by linarith only [data.cosineLarge]) data.sinePositive.le E.unit_normal
    linarith only [strict,sep,face,data.sideLarge,cap,data.cosineLarge,data.sineSmall]
  · have high := floor_upper E data floor
    linarith only [strict,sep,high,data.cosineLarge,data.sineSmall]

private theorem negative_support (W E : OpenSquare) (r : ℝ) (signed : W.s= -r)
    (wp : 0<W.c) (rn : 0≤r) (order : r≤W.c)
    (data : PositiveEndingFaces.Data E) :
    lower E W.c (-r)<1-W.c ∧ lower E W.c (-r)<7/100 := by
  have cp : 0<E.c := by linarith only [data.cosineLarge]
  have sp := data.sinePositive
  have bounds := CommonCases.CanonicalScalars.bounds E.c E.s cp sp.le data.ordered E.unit_normal
  have unit : W.c^2+r^2=1 := by simpa only [signed,neg_sq] using W.unit_normal
  have wBounds := CommonCases.CanonicalScalars.bounds W.c r wp rn order unit
  let k := E.c*W.c-E.s*r
  let h := E.s*W.c+E.c*r
  have kn : 0≤k := by
    have first := mul_nonneg wp.le (sub_nonneg.mpr data.ordered)
    have last := mul_nonneg sp.le (sub_nonneg.mpr order)
    dsimp only [k]
    nlinarith only [first,last]
  have hp : 0<h := by
    have first := mul_pos sp wp
    have last := mul_nonneg cp.le rn
    dsimp only [h]
    nlinarith only [first,last]
  have formula := SupportBands.lower_pn E W.c (-r)
    (by dsimp only [k] at kn; nlinarith only [kn])
    (by dsimp only [h] at hp; nlinarith only [hp])
  have lowerFormula : lower E W.c (-r)=k*E.loU-h*(E.loV+E.side) := by
    rw [formula]
    dsimp only [k,h]
    ring
  rcases data.bar with face | floor
  · let D := (E.c-1)*(E.c+E.s)+(13/50)*E.s^2
    let R := (E.c-1)*(E.c-E.s)+(13/50)*E.c*E.s
    have first := mul_nonneg kn (sub_nonneg.mpr data.upperU)
    have last := mul_nonneg hp.le
      (show 0≤E.loV+E.c+(13/50)*E.s by linarith only [face])
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<k+h by linarith only [kn,hp])
    have strict : lower E W.c (-r)<W.c*D+r*R := by
      rw [lowerFormula]
      dsimp only [k,h,D,R] at first last extra ⊢
      nlinarith only [first,last,extra]
    have norm := PositiveEndingScalars.bar_norm E.c E.s W.c r
      (by linarith only [data.cosineLarge]) sp E.unit_normal unit
    have margins := PositiveEndingScalars.bar_bounds E.c E.s
      (by linarith only [data.cosineLarge]) sp data.sineSmall E.unit_normal
    have firstNegative := mul_neg_of_pos_of_neg wp margins.1
    have lastUpper := mul_nonneg rn (show 0≤7/100-R by exact sub_nonneg.mpr margins.2.le)
    have rUpper : r≤1 := by linarith only [order,wBounds.2.1]
    dsimp only [D,R] at strict lastUpper
    exact ⟨by linarith only [strict,norm],
      by nlinarith only [strict,firstNegative,lastUpper,rUpper]⟩
  · have first := mul_nonneg hp.le (show 0≤E.s*E.loU+E.c*E.loV+1 by
      linarith only [floor])
    have last := mul_nonneg wp.le (sub_nonneg.mpr data.upperU)
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<W.c+E.c*h by
        have product := mul_pos cp hp
        linarith only [wp,product])
    have identity : E.c*(k*E.loU-h*(E.loV+E.side))+
        h*(E.s*E.loU+E.c*E.loV+1)+W.c*(E.c-(E.loU+E.side))+
        (E.side-1)*(W.c+E.c*h)=(1-E.c)*(h-W.c) := by
      dsimp only [k,h]
      linear_combination W.c*E.loU*E.unit_normal
    have scaled : E.c*(lower E W.c (-r))<(1-E.c)*(h-W.c) := by
      rw [lowerFormula]
      nlinarith only [first,last,extra,identity]
    have norm := PositiveEndingScalars.floor_norm E.c E.s W.c r
      (by linarith only [data.cosineLarge]) sp
      (by linarith only [data.sineSmall]) E.unit_normal unit
    have firstResult : lower E W.c (-r)<1-W.c := by
      apply (mul_lt_mul_iff_right₀ cp).mp
      dsimp only [h] at scaled
      linarith only [scaled,norm]
    have orderWeight := mul_nonneg cp.le (sub_nonneg.mpr order)
    have sumWeight := mul_nonneg wp.le
      (show 0≤3/7-(E.c+E.s-1) by linarith only [bounds.2.2.2.1])
    have hSmall : h-W.c<1/2 := by
      dsimp only [h]
      nlinarith only [orderWeight,sumWeight,wBounds.2.1]
    have remainder := mul_nonneg (sub_nonneg.mpr data.cosineUpper)
      (show 0≤1/2-(h-W.c) by linarith only [hSmall])
    have secondResult : lower E W.c (-r)<1/18 := by
      apply (mul_lt_mul_iff_right₀ cp).mp
      nlinarith only [scaled,remainder,data.cosineLarge]
    exact ⟨firstResult,by linarith only [secondResult]⟩

theorem negative_w_axis (W E : OpenSquare) (r : ℝ) (signed : W.s= -r)
    (wp : 0<W.c) (rn : 0≤r) (order : r≤W.c)
    (side : 1<W.side) (cap : W.side≤1001/1000)
    (data : PositiveEndingFaces.Data E)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (avoid : ∀ y : ℝ,0≤y → y≤4/5 → ¬W.Inside (-1) y)
    (sep : upper W W.c W.s≤lower E W.c W.s) : False := by
  have bounds := negative_support W E r signed wp rn order data
  have faces := PositiveEndingWalls.negative W r signed side cap wp rn order west center avoid
  have own := (ownU W).2
  rw [own,signed] at sep
  rcases faces with lower | stronger
  · linarith only [sep,bounds.1,lower,side]
  · linarith only [sep,bounds.2,stronger]

theorem positive_w_axis (W E : OpenSquare)
    (wp : 0<W.c) (rn : 0≤W.s) (order : W.s≤W.c)
    (side : 1<W.side) (cap : W.side≤1001/1000)
    (data : PositiveEndingFaces.Data E)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (missingZ : ¬W.Inside 0 (-C1092WallProfileScalars.half E.c E.s))
    (avoid : ∀ y : ℝ,0≤y → y≤4/5 → ¬W.Inside (-1) y)
    (sep : upper W W.s (-W.c)≤lower E W.s (-W.c)) : False := by
  have cp : 0<E.c := by linarith only [data.cosineLarge]
  have sp := data.sinePositive
  let delta := E.c*W.s-E.s*W.c
  let k := E.c*W.c+E.s*W.s
  have kp : 0<k := by
    have first := mul_pos cp wp
    have last := mul_nonneg sp.le rn
    dsimp only [k]
    nlinarith only [first,last]
  have unit : k^2+delta^2=1 := by
    dsimp only [k,delta]
    calc
      _ = (E.c^2+E.s^2)*(W.c^2+W.s^2) := by ring
      _ = _ := by rw [E.unit_normal,W.unit_normal]; norm_num
  have ku : k≤1 := by nlinarith only [unit,sq_nonneg delta,sq_nonneg (k-1)]
  have wBounds := CommonCases.CanonicalScalars.bounds W.c W.s wp rn order W.unit_normal
  have margins := PositiveEndingWalls.positive W (C1092WallProfileScalars.half E.c E.s)
    side cap wp rn order data.halfPositive data.halfSmall west center missingZ avoid
  have own : upper W W.s (-W.c)= -W.loV := by
    have h := WallProfile.upper_neg W (-W.s) W.c
    simpa only [neg_neg,(ownV W).1] using h
  rw [own] at sep
  rcases data.bar with face | floor
  · let B := 1-E.c-(13/50)*E.s
    have high : B<E.loV+E.side := by dsimp only [B]; linarith only [face,data.sideLarge]
    have last := mul_pos kp (sub_pos.mpr high)
    have projection : lower E W.s (-W.c)< -k*B := by
      by_cases sign : 0≤delta
      · have formula := SupportBands.lower_pn E W.s (-W.c)
          (by dsimp only [delta] at sign; nlinarith only [sign])
          (by dsimp only [k] at kp; nlinarith only [kp])
        have uNegative : E.loU<0 := by linarith only [data.upperU,data.sideLarge,data.cosineUpper]
        have first := mul_nonpos_of_nonneg_of_nonpos sign uNegative.le
        rw [formula]
        dsimp only [delta,k] at first last ⊢
        nlinarith only [first,last]
      · have sign' : delta≤0 := le_of_not_ge sign
        have formula := SupportBands.lower_nn E W.s (-W.c)
          (by dsimp only [delta] at sign'; nlinarith only [sign'])
          (by dsimp only [k] at kp; nlinarith only [kp])
        have first := mul_nonpos_of_nonpos_of_nonneg sign' data.upperUPositive.le
        rw [formula]
        dsimp only [delta,k] at first last ⊢
        nlinarith only [first,last]
    have cap := InwardSignScalars.projection_cap E.c E.s cp sp.le E.unit_normal
    by_cases sign : 0≤B
    · have nonpositive := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr kp.le) sign
      linarith only [projection,sep,margins.1,nonpositive]
    · have remainder := mul_nonneg (sub_nonneg.mpr ku) (neg_nonneg.mpr (le_of_not_ge sign))
      dsimp only [B] at projection remainder
      nlinarith only [projection,sep,margins.1,remainder,cap]
  · have lowerBound := SupportBands.lower_bound_pn E W.s (-W.c)
      (by dsimp only [k] at kp; nlinarith only [kp])
    have lowerScaled := mul_le_mul_of_nonneg_left lowerBound cp.le
    have first := mul_nonneg kp.le (show 0≤E.s*E.loU+E.c*E.loV+1 by
      linarith only [floor])
    have last := mul_nonneg rn (sub_nonneg.mpr data.upperU)
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<W.s+E.c*k by
        have product := mul_pos cp kp
        linarith only [rn,product])
    have identity : E.c*(delta*E.loU-k*(E.loV+E.side))+
        k*(E.s*E.loU+E.c*E.loV+1)+W.s*(E.c-(E.loU+E.side))+
        (E.side-1)*(W.s+E.c*k)=(1-E.c)*(k-W.s) := by
      dsimp only [delta,k]
      linear_combination W.s*E.loU*E.unit_normal
    have scaled : E.c*(lower E W.s (-W.c))<(1-E.c)*(k-W.s) := by
      dsimp only [delta,k] at identity first last extra ⊢
      nlinarith only [lowerScaled,first,last,extra,identity]
    have rSmall : W.s<1 := by
      by_contra bad
      have large : 1≤W.s := le_of_not_gt bad
      have square := mul_nonneg (sub_nonneg.mpr large)
        (show 0≤W.s+1 by linarith only [rn])
      nlinarith only [W.unit_normal,square,sq_pos_of_pos wp]
    have firstRemainder := mul_nonneg (sub_nonneg.mpr data.cosineUpper) (sub_nonneg.mpr ku)
    have lastRemainder := mul_pos (sub_pos.mpr rSmall)
      (show 0<(12/113)*E.c-(1-E.c) by linarith only [data.cosineLarge])
    have strict : lower E W.s (-W.c)<(12/113)*(1-W.s) := by
      apply (mul_lt_mul_iff_right₀ cp).mp
      nlinarith only [scaled,firstRemainder,lastRemainder]
    linarith only [strict,sep,margins.2]

#print axioms own_axis
#print axioms negative_w_axis
#print axioms positive_w_axis
end N12Compact.Completion.OtherCases.PositiveEndingSupports
