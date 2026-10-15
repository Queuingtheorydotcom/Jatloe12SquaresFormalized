import Compact.Completion.C1092.MMMMPairScalars

/-! The final MMMM cancellation. The two hypotheses concern the same U,V
and common side a; the exact positive margin is 4369/140000. -/
namespace N12Compact.C1092MMMMCancellation
open C977CornerCubic C1092MMMMPairScalars
set_option Elab.async false

theorem impossible {a d r b t B T U V : ℝ} (dn : Normal d r)
    (en : Normal b t) (wn : Normal B T) (ha : 1 < a)
    (small : r < 7/50) (close : 99/100 < d)
    (esteep : 9/20 < t) (wsteep : 9/20 < T)
    (ecos : b < 9/10) (wcos : B < 9/10)
    (uLow : U < 0) (vLow : V < 0)
    (east : a*(1+b*r+t*d) ≤ b+t+(b*d-t*r)*V-(b*r+t*d)*U)
    (west : a*(1+T*d-B*r) ≤ B+T+(B*d+T*r)*U-(T*d-B*r)*V) : False := by
  let ae := b*d-t*r
  let aw := B*d+T*r
  let ke := b*r+t*d
  let kw := T*d-B*r
  let DE := 1+ke-b-t
  let DW := 1+kw-B-T
  have db := normal_bounds dn
  have eb := normal_bounds en
  have wb := normal_bounds wn
  have dp : 0 < d := by linarith only [db.1]
  have ep : 0 < b := by linarith only [eb.1]
  have wp : 0 < B := by linarith only [wb.1]
  have tp : 0 < t := by linarith only [esteep]
  have Tp : 0 < T := by linarith only [wsteep]
  have kep : 0 < ke := by
    have first := mul_nonneg ep.le dn.1
    have last := mul_pos tp dp
    dsimp [ke]; linarith only [first,last]
  have kwn : 0 ≤ kw := by
    have first := mul_lt_mul_of_pos_left close Tp
    have last := mul_nonneg dn.1 (show 0≤9/10-B by linarith only [wcos])
    dsimp [kw]
    nlinarith only [first,last,wsteep,small]
  have awLower : 693/1000 < aw := by
    have first := mul_lt_mul_of_pos_left close wp
    have last := mul_nonneg (by norm_num : (0:ℝ)≤99/100)
      (show 0≤B-7/10 by linarith only [wb.1])
    have cross := mul_nonneg wn.1 dn.1
    dsimp [aw]; nlinarith only [first,last,cross]
  have awp : 0 < aw := by linarith only [awLower]
  have crossUnit : ke^2+(b*d-t*r)^2=1 := by
    dsimp [ke]
    calc
      _ = (b^2+t^2)*(d^2+r^2) := by ring
      _ = 1 := by rw [en.2.2,dn.2.2]; norm_num
  have keu : ke ≤ 1 := by nlinarith only [crossUnit,sq_nonneg (b*d-t*r),sq_nonneg (ke-1)]
  have dn0 : 0 ≤ 1-d := sub_nonneg.mpr db.2.1
  have dn1 : 1-d ≤ 1/100 := by linarith only [close]
  have tTail : t*(1-d) ≤ 1/140 := by
    have first := mul_le_mul (sine_bound en) dn1 dn0 (by norm_num : (0:ℝ)≤5/7)
    nlinarith only [first]
  have TTail : T*(1-d) ≤ 1/140 := by
    have first := mul_le_mul (sine_bound wn) dn1 dn0 (by norm_num : (0:ℝ)≤5/7)
    nlinarith only [first]
  have br := mul_nonneg ep.le dn.1
  have DElower : 13/140 < DE := by dsimp [DE,ke]; nlinarith only [ecos,br,tTail]
  have Br : B*r ≤ 63/500 := by
    have first := mul_le_mul wcos.le small.le dn.1 (by norm_num : (0:ℝ)≤9/10)
    nlinarith only [first]
  have DWlower : -29/875 < DW := by dsimp [DW,kw]; nlinarith only [wcos,Br,TTail]
  have DEp : 0 < DE := by linarith only [DElower]
  have firstMargin := mul_lt_mul_of_pos_right awLower DEp
  have baseMargin := mul_lt_mul_of_pos_left DElower (by norm_num : (0:ℝ)<693/1000)
  have lastMargin : -29/875 < ke*DW := by
    by_cases sign : 0 ≤ DW
    · have product := mul_nonneg kep.le sign
      linarith only [product]
    · have weight := mul_nonneg (sub_nonneg.mpr keu) (show 0≤-DW by linarith only [sign])
      nlinarith only [weight,DWlower]
  have margin : 4369/140000 < aw*DE+ke*DW := by
    nlinarith only [firstMargin,baseMargin,lastMargin]
  have strictE := mul_pos (sub_pos.mpr ha) (show 0<1+ke by linarith only [kep])
  have strictW := mul_pos (sub_pos.mpr ha) (show 0<1+kw by linarith only [kwn])
  have e : DE < ae*V-ke*U := by
    dsimp [DE,ae,ke] at strictE ⊢
    nlinarith only [east,strictE]
  have w : DW < aw*U-kw*V := by
    dsimp [DW,aw,kw] at strictW ⊢
    nlinarith only [west,strictW]
  have eWeight := mul_lt_mul_of_pos_left e awp
  have wWeight := mul_lt_mul_of_pos_left w kep
  have coefficient : ae*aw-ke*kw=b*B-t*T := by
    dsimp [ae,aw,ke,kw]
    linear_combination (b*B-t*T)*dn.2.2
  have coefficientV := congrArg (fun z : ℝ => z*V) coefficient
  dsimp at coefficientV
  have first := mul_nonneg (sub_nonneg.mpr en.2.1) wp.le
  have last := mul_nonneg en.1 (sub_nonneg.mpr wn.2.1)
  have cn : 0 ≤ b*B-t*T := by nlinarith only [first,last]
  have negative := mul_nonpos_of_nonneg_of_nonpos cn vLow.le
  nlinarith only [eWeight,wWeight,coefficientV,negative,margin]

#print axioms impossible
end N12Compact.C1092MMMMCancellation
