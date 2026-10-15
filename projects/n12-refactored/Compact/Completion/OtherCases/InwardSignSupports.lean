import Compact.Completion.OtherCases.BottomBarSupport
import Compact.Completion.OtherCases.SupportBands
import Compact.Completion.OtherCases.InwardSignScalars
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! Full support obstructions for a nonnegative inward southeast square.
The actual bottom bar gives two exhaustive alternatives; both are compared
against each surviving true western or southeast face normal. -/
namespace N12Compact.Completion.OtherCases.InwardSignSupports
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

structure Data (E : OpenSquare) : Prop where
  cosinePositive : 0<E.c
  sinePositive : 0<E.s
  ordered : E.s≤E.c
  sideLarge : 1<E.side
  upperU : E.loU+E.side≤E.c-(13/50)*E.s
  upperV : E.loV+E.side≤0
  bar : -(13/50)*E.s-E.c≤E.loV ∨ -1≤E.s*E.loU+E.c*E.loV

theorem own_axis (W E : OpenSquare) (data : Data E)
    (west : W.Inside (-7/20) (-7/20))
    (sep : upper W E.s (-E.c)≤lower E E.s (-E.c)) : False := by
  have cp := data.cosinePositive
  have sp := data.sinePositive
  have bounds := CommonCases.CanonicalScalars.bounds E.c E.s cp sp.le data.ordered E.unit_normal
  have unit : E.s^2+(-E.c)^2=1 := by nlinarith only [E.unit_normal]
  have strict := (strict_bounds W _ _ E.s (-E.c) unit west).2
  have own : lower E E.s (-E.c)= -(E.loV+E.side) := by
    have h := WallProfile.lower_neg E (-E.s) E.c
    simpa only [neg_neg,(ownV E).2] using h
  rw [own] at sep
  rcases data.bar with face | floor
  · have span : 1<E.c+(13/50)*E.s := by
      linarith only [face,data.upperV,data.sideLarge]
    have arc := InwardSignScalars.short_arc E.c E.s cp sp E.unit_normal span
    have cap := InwardSignScalars.projection_cap E.c E.s cp sp.le E.unit_normal
    linarith only [strict,sep,face,data.sideLarge,arc.1,arc.2,cap]
  · have uWeight := mul_nonneg sp.le (sub_nonneg.mpr data.upperU)
    have vWeight := mul_pos cp (show 0< -(7/20)*(E.c-E.s)-(E.loV+E.side) by
      linarith only [strict,sep])
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<E.c+E.s by linarith only [cp,sp])
    have margin := mul_nonneg (sub_nonneg.mpr data.ordered)
      (show 0≤(29/100)*E.c-(13/50)*E.s by linarith only [data.ordered,cp])
    nlinarith only [floor,uWeight,vWeight,extra,margin,bounds.2.2.2.2,sq_nonneg E.c]

theorem negative_w_axis (W E : OpenSquare) (r : ℝ) (signed : W.s= -r)
    (wp : 0<W.c) (rn : 0≤r) (order : r≤W.c)
    (data : Data E) (center : W.Inside 0 0)
    (sep : upper W W.c W.s≤lower E W.c W.s) : False := by
  have cp := data.cosinePositive
  have sp := data.sinePositive
  have bounds := CommonCases.CanonicalScalars.bounds E.c E.s cp sp.le data.ordered E.unit_normal
  let k := E.c*W.c-E.s*r
  let h := E.s*W.c+E.c*r
  have kNonnegative : 0≤k := by
    have first := mul_nonneg wp.le (sub_nonneg.mpr data.ordered)
    have last := mul_nonneg sp.le (sub_nonneg.mpr order)
    dsimp only [k]
    nlinarith only [first,last]
  have hPositive : 0<h := by
    have first := mul_pos sp wp
    have last := mul_nonneg cp.le rn
    dsimp only [h]
    nlinarith only [first,last]
  have strict := (strict_bounds W 0 0 W.c W.s W.unit_normal center).2
  rw [signed] at sep strict
  have formula := SupportBands.lower_pn E W.c (-r)
    (by dsimp only [k] at kNonnegative; nlinarith only [kNonnegative])
    (by dsimp only [h] at hPositive; nlinarith only [hPositive])
  have lower : lower E W.c (-r)=k*E.loU-h*(E.loV+E.side) := by
    rw [formula]
    dsimp only [k,h]
    ring
  rw [lower] at sep
  have positive : 0<k*E.loU-h*(E.loV+E.side) := by
    linarith only [sep,strict]
  rcases data.bar with face | floor
  · have first := mul_nonneg kNonnegative (sub_nonneg.mpr data.upperU)
    have last := mul_nonneg hPositive.le (show 0≤E.loV+E.c+(13/50)*E.s by
      linarith only [face])
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<k+h by linarith only [kNonnegative,hPositive])
    have margin := InwardSignScalars.negative_bar E.c E.s W.c r cp sp data.ordered
      E.unit_normal wp rn order
    dsimp only [k,h] at first last extra positive
    nlinarith only [first,last,extra,positive,margin]
  · have first := mul_nonneg hPositive.le (show 0≤E.s*E.loU+E.c*E.loV+1 by
      linarith only [floor])
    have last := mul_nonneg wp.le (sub_nonneg.mpr data.upperU)
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<W.c+h*E.c by
        have product := mul_pos hPositive cp
        linarith only [wp,product])
    have orderWeight := mul_nonneg (show 0≤1-E.c by linarith only [bounds.2.1])
      (mul_nonneg cp.le (sub_nonneg.mpr order))
    have identity :
        E.c*(k*E.loU-h*(E.loV+E.side))+
          h*(E.s*E.loU+E.c*E.loV+1)+
          W.c*(E.c-(13/50)*E.s-(E.loU+E.side))+
          (E.side-1)*(W.c+h*E.c)+(1-E.c)*E.c*(W.c-r) =
        W.c*((1-E.c)*(E.c+E.s-1)-(13/50)*E.s) := by
      dsimp only [k,h]
      linear_combination W.c*E.loU*E.unit_normal
    have positiveScaled := mul_pos cp positive
    have margin := mul_neg_of_pos_of_neg wp
      (InwardSignScalars.x_negative E.c E.s cp sp data.ordered E.unit_normal)
    nlinarith only [first,last,extra,orderWeight,identity,positiveScaled,margin]

theorem positive_w_axis (W E : OpenSquare)
    (wp : 0<W.c) (rn : 0≤W.s) (order : W.s≤W.c)
    (data : Data E) (west : W.Inside (-7/20) (-7/20))
    (elbow : E.Inside (13/50) 0)
    (sep : upper W W.s (-W.c)≤lower E W.s (-W.c)) : False := by
  have cp := data.cosinePositive
  have sp := data.sinePositive
  have bounds := CommonCases.CanonicalScalars.bounds E.c E.s cp sp.le data.ordered E.unit_normal
  let delta := E.c*W.s-E.s*W.c
  let k := E.c*W.c+E.s*W.s
  have kPositive : 0<k := by
    have first := mul_pos cp wp
    have last := mul_nonneg sp.le rn
    dsimp only [k]
    nlinarith only [first,last]
  have unit : W.s^2+(-W.c)^2=1 := by nlinarith only [W.unit_normal]
  have strict := (strict_bounds W _ _ W.s (-W.c) unit west).2
  have projection : (7/20)*(W.c-W.s)<lower E W.s (-W.c) := by
    linarith only [strict,sep]
  rcases data.bar with face | floor
  · by_cases sign : 0≤delta
    · have formula := SupportBands.lower_pn E W.s (-W.c)
        (by dsimp only [delta] at sign; nlinarith only [sign])
        (by dsimp only [k] at kPositive; nlinarith only [kPositive])
      have lower : lower E W.s (-W.c)=delta*E.loU-k*(E.loV+E.side) := by
        rw [formula]
        dsimp only [delta,k]
        ring
      rw [lower] at projection
      have first := mul_nonneg sign (sub_nonneg.mpr data.upperU)
      have last := mul_nonneg kPositive.le (show 0≤E.loV+E.c+(13/50)*E.s by
        linarith only [face])
      have extra := mul_pos (sub_pos.mpr data.sideLarge)
        (show 0<delta+k by linarith only [sign,kPositive])
      have margin := InwardSignScalars.positive_bar E.c E.s W.c W.s cp sp data.ordered
        E.unit_normal wp rn order
      dsimp only [delta,k] at first last extra projection
      nlinarith only [first,last,extra,projection,margin]
    · have negative : delta≤0 := le_of_not_ge sign
      have formula := SupportBands.lower_nn E W.s (-W.c)
        (by dsimp only [delta] at negative; nlinarith only [negative])
        (by dsimp only [k] at kPositive; nlinarith only [kPositive])
      have lower : lower E W.s (-W.c)=
          delta*(E.loU+E.side)-k*(E.loV+E.side) := by
        rw [formula]
        dsimp only [delta,k]
        ring
      rw [lower] at projection
      have span : 1<E.c+(13/50)*E.s := by
        linarith only [face,data.upperV,data.sideLarge]
      have arc := InwardSignScalars.short_arc E.c E.s cp sp E.unit_normal span
      have cap := InwardSignScalars.projection_cap E.c E.s cp sp.le E.unit_normal
      have turn := InwardSignScalars.difference_order E.c E.s W.c W.s cp sp.le wp rn
        E.unit_normal W.unit_normal (by dsimp only [delta] at negative; exact negative)
      have kUnit : k^2+delta^2=1 := by
        dsimp only [k,delta]
        calc
          _ = (E.c^2+E.s^2)*(W.c^2+W.s^2) := by ring
          _ = _ := rw [E.unit_normal,W.unit_normal]; norm_num
      have kUpper : k≤1 := by nlinarith only [kUnit,sq_nonneg delta,sq_nonneg (k-1)]
      have upperPositive : 0<E.loU+E.side := by
        linarith only [elbow.2.1,cp]
      have first := mul_nonpos_of_nonpos_of_nonneg negative upperPositive.le
      have last := mul_pos kPositive
        (show 0<E.loV+E.side-(1-E.c-(13/50)*E.s) by linarith only [face,data.sideLarge])
      have remainder := mul_nonneg (sub_nonneg.mpr kUpper)
        (show 0≤E.c+(13/50)*E.s-1 by linarith only [span])
      nlinarith only [projection,turn,arc.1,arc.2,cap,first,last,remainder]
  · have lower := SupportBands.lower_bound_pn E W.s (-W.c)
      (by dsimp only [k] at kPositive; nlinarith only [kPositive])
    have positive : 0<E.c*(delta*E.loU-k*(E.loV+E.side)-(7/20)*(W.c-W.s)) := by
      apply mul_pos cp
      dsimp only [delta,k]
      nlinarith only [lower,projection]
    have first := mul_nonneg kPositive.le (show 0≤E.s*E.loU+E.c*E.loV+1 by
      linarith only [floor])
    have last := mul_nonneg rn (sub_nonneg.mpr data.upperU)
    have extra := mul_pos (sub_pos.mpr data.sideLarge)
      (show 0<W.s+k*E.c by
        have product := mul_pos kPositive cp
        linarith only [rn,product])
    have identity :
        E.c*(delta*E.loU-k*(E.loV+E.side)-(7/20)*(W.c-W.s))+
          k*(E.s*E.loU+E.c*E.loV+1)+
          W.s*(E.c-(13/50)*E.s-(E.loU+E.side))+
          (E.side-1)*(W.s+k*E.c) =
        W.c*(E.c*(13/20-E.c))+
          W.s*((1-E.c)*(E.s-1)-(13/50)*E.s+(7/20)*E.c) := by
      dsimp only [delta,k]
      linear_combination W.s*E.loU*E.unit_normal
    have margin := InwardSignScalars.positive_floor E.c E.s W.c W.s cp sp data.ordered
      E.unit_normal wp rn order
    nlinarith only [positive,first,last,extra,identity,margin]

#print axioms own_axis
#print axioms negative_w_axis
#print axioms positive_w_axis
end N12Compact.Completion.OtherCases.InwardSignSupports

