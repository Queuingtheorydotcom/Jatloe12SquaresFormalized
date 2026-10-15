import Compact.Completion.OtherCases.PositiveEndingFaces
import Compact.Completion.OtherCases.DerivedWalls

/-! Complete left-wall alternatives from the one genuine western bar.
Every possible line intersection is first located inside that actual bar;
the resulting half-plane then bounds the full closed square vertex. -/
namespace N12Compact.Completion.OtherCases.PositiveEndingWalls
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem negative (W : OpenSquare) (r : ℝ) (signed : W.s= -r)
    (side : 1<W.side) (cap : W.side≤1001/1000)
    (dp : 0<W.c) (rn : 0≤r) (order : r≤W.c)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (avoid : ∀ y : ℝ,0≤y → y≤4/5 → ¬W.Inside (-1) y) :
    -W.c≤W.loU ∨ 1/14<W.loU+W.side := by
  by_cases face : -W.c≤W.loU
  · exact Or.inl face
  right
  have unit : W.c^2+r^2=1 := by simpa only [signed,neg_sq] using W.unit_normal
  have bounds := CommonCases.CanonicalScalars.bounds W.c r dp rn order unit
  have p := west
  have o := center
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg,mul_zero,zero_mul,
    add_zero,zero_add] at p o
  have vFace : -r≤W.loV := by
    apply le_of_not_gt
    intro low
    exact avoid 0 le_rfl (by norm_num) (by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg,mul_zero,mul_one,
        zero_mul,add_zero,zero_add]
      refine ⟨?_,?_,low,?_⟩ <;> linarith only [face,o.2.1,o.2.2.2,dp,rn])
  have slope : 7*W.c<13*r := by linarith only [p.2.2.1,vFace]
  have rLarge : 3/8<r := by linarith only [slope,bounds.1]
  have rp : 0<r := by linarith only [rLarge]
  have coefficient : 0≤1+W.c-2*r := by linarith only [order,bounds.2.1]
  have product := mul_nonneg rn coefficient
  have scaled : 0≤(1+W.c)*(r/2-(1-W.c)) := by nlinarith only [product,unit]
  have halfGap := nonneg_of_mul_nonneg_right scaled
    (show 0<1+W.c by linarith only [dp])
  have halfBound : 1-W.c≤r/2 := by linarith only [halfGap]
  have line : ∀ y : ℝ,¬W.Inside (-1) y := by
    intro y own
    have point := own
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_neg,mul_one,
      neg_mul] at point
    have low : 0<y := by
      have positive : 0<W.c*y := by linarith only [point.2.2.1,vFace]
      exact (mul_pos_iff_of_pos_left dp).mp positive
    have high : y<4/5 := by
      apply (mul_lt_mul_left rp).mp
      nlinarith only [point.1,o.2.1,cap,halfBound,rLarge]
    exact avoid y low.le high.le own
  have wall := DerivedWalls.vertical_right W 0 0 (-1) center (by norm_num) line
  have closed := WallProfile.vertex W W.loU W.loV
    ⟨le_rfl,by linarith only [W.side_pos]⟩
    ⟨le_rfl,by linarith only [W.side_pos]⟩
  have floor := DerivedWalls.closed_affine_bound W 1 0 (-1) 0 0
    (by intro x y own; simpa only [one_mul,zero_mul,add_zero] using wall x y own)
    center _ _ closed
  rw [signed] at floor
  have upperWeight := mul_pos dp (sub_pos.mpr side)
  have lastWeight := mul_pos rp
    (show 0< -(7/20)*(r+W.c)-W.loV by linarith only [p.2.2.1])
  have margin := PositiveEndingScalars.negative_west_margin W.c r dp rn order unit slope
  have scaled : W.c*(1/14)<W.c*(W.loU+W.side) := by
    nlinarith only [floor,upperWeight,lastWeight,margin]
  exact (mul_lt_mul_left dp).mp scaled

private theorem left_line_margin (d r : ℝ) (dp : 0<d) (rn : 0≤r)
    (order : r≤d) (unit : d^2+r^2=1) (slope : 5*d<14*r) :
    1001/1000<(4/5)*d+r := by
  have bounds := CommonCases.CanonicalScalars.bounds d r dp rn order unit
  by_contra bad
  have low : (4/5)*d+r≤1001/1000 := le_of_not_gt bad
  have dSmall : d<87/100 := by linarith only [low,slope]
  have rLarge : 49/100<r := by
    by_contra failed
    have rSmall : r≤49/100 := le_of_not_gt failed
    have first := mul_nonneg (sub_nonneg.mpr dSmall.le)
      (show 0≤87/100+d by linarith only [dp])
    have last := mul_nonneg (sub_nonneg.mpr rSmall)
      (show 0≤49/100+r by linarith only [rn])
    nlinarith only [unit,first,last]
  linarith only [low,bounds.1,rLarge]

theorem positive (W : OpenSquare) (z : ℝ) (side : 1<W.side)
    (cap : W.side≤1001/1000) (dp : 0<W.c) (rn : 0≤W.s) (order : W.s≤W.c)
    (zp : 0<z) (zu : z<9/40)
    (west : W.Inside (-7/20) (-7/20)) (center : W.Inside 0 0)
    (missingZ : ¬W.Inside 0 (-z))
    (avoid : ∀ y : ℝ,0≤y → y≤4/5 → ¬W.Inside (-1) y) :
    7/200< -W.loV ∧ (12/113)*(1-W.s)< -W.loV := by
  have bounds := CommonCases.CanonicalScalars.bounds W.c W.s dp rn order W.unit_normal
  have p := west
  have o := center
  simp only [OpenSquare.Inside,InBands,mul_neg,mul_zero,zero_mul,add_zero,zero_add]
    at p o
  have zLowerU : W.loU< -W.s*z := by
    have extra := mul_nonneg rn (show 0≤7/20-z by linarith only [zu])
    nlinarith only [p.1,extra,dp]
  have zProduct := mul_nonneg rn zp.le
  have zCosine := mul_pos dp zp
  have vFace : -W.c*z≤W.loV := by
    apply le_of_not_gt
    intro low
    apply missingZ
    simpa only [OpenSquare.Inside,InBands,mul_zero,neg_zero,zero_add,mul_neg,neg_mul] using
      And.intro zLowerU (And.intro (by nlinarith only [o.2.1,zProduct])
        (And.intro low (by nlinarith only [o.2.2.2,zCosine])))
  have strictZ := mul_pos dp (show 0<9/40-z by linarith only [zu])
  have slope : 5*W.c<14*W.s := by nlinarith only [p.2.2.1,vFace,strictZ]
  have rp : 0<W.s := by linarith only [slope,dp]
  have rSmall : W.s<3/4 := by
    have difference := mul_nonneg (sub_nonneg.mpr order) (add_nonneg dp.le rn)
    by_contra bad
    have large : 3/4≤W.s := le_of_not_gt bad
    have square := mul_nonneg (sub_nonneg.mpr large)
      (show 0≤W.s+3/4 by linarith only [rn])
    nlinarith only [W.unit_normal,difference,square]
  have lowerU : -W.c≤W.loU := by
    apply le_of_not_gt
    intro low
    exact avoid 0 le_rfl (by norm_num) (by
      simp only [OpenSquare.Inside,InBands,mul_neg,mul_one,mul_zero,zero_mul,add_zero,neg_neg]
      refine ⟨low,?_,?_,?_⟩
      · linarith only [o.2.1,dp]
      · linarith only [o.2.2.1,rn]
      · have product := mul_nonneg (sub_nonneg.mpr bounds.2.1) zp.le
        nlinarith only [vFace,side,zu,rSmall,product])
  have margin := left_line_margin W.c W.s dp rn order W.unit_normal slope
  have line : ∀ y : ℝ,¬W.Inside (-1) y := by
    intro y own
    have point := own
    simp only [OpenSquare.Inside,InBands,mul_neg,mul_one,neg_mul,neg_neg] at point
    have low : 0<y := by
      have positive : 0<W.s*y := by linarith only [point.1,lowerU]
      exact (mul_pos_iff_of_pos_left rp).mp positive
    have high : y<4/5 := by
      apply (mul_lt_mul_left dp).mp
      linarith only [point.2.2.2,p.2.2.1,cap,order,margin]
    exact avoid y low.le high.le own
  have wall := DerivedWalls.vertical_right W 0 0 (-1) center (by norm_num) line
  have closed := WallProfile.vertex W W.loU (W.loV+W.side)
    ⟨le_rfl,by linarith only [W.side_pos]⟩
    ⟨by linarith only [W.side_pos],le_rfl⟩
  have floor := DerivedWalls.closed_affine_bound W 1 0 (-1) 0 0
    (by intro x y own; simpa only [one_mul,zero_mul,add_zero] using wall x y own)
    center _ _ closed
  have first : (7/20)*(W.c-W.s)< -W.loV := by linarith only [p.2.2.1]
  have cancel : W.s*((13/20)/W.s)=13/20 := by
    rw [mul_comm,div_mul_cancel₀ _ rp.ne']
  have identity : W.s*((7/20)*(W.c-W.s)+1-(13/20)/W.s)=
      (7/20)*W.s*(W.c-W.s)+W.s-13/20 := by
    rw [mul_sub,cancel]
    ring
  have strictU := mul_pos dp
    (show 0< -(7/20)*(W.c+W.s)-W.loU by linarith only [p.1])
  have strictSide := mul_pos rp (sub_pos.mpr side)
  have scaled : W.s*((7/20)*(W.c-W.s)+1-(13/20)/W.s)<W.s*(-W.loV) := by
    nlinarith only [floor,strictU,strictSide,identity,W.unit_normal]
  have second := (mul_lt_mul_left rp).mp scaled
  have margins := PositiveEndingScalars.positive_west_margin W.c W.s dp rn order W.unit_normal
  constructor
  · rcases margins.1 with left | right
    · linarith only [left,first]
    · linarith only [right,second]
  · rcases margins.2 with left | right
    · linarith only [left,first]
    · linarith only [right,second]

#print axioms negative
#print axioms positive
end N12Compact.Completion.OtherCases.PositiveEndingWalls
