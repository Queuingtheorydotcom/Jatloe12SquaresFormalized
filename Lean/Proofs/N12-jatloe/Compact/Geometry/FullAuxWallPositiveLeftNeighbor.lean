import Compact.Geometry.FullAuxWallSmallPositiveLeftB

/-! The opposite central square's own U separator cannot coexist with
the genuine left wall once that wall has sine at least 4/25. The argument
compares support margins on the whole canonical arc; two broad intervals
replace any enumeration of angles. -/
namespace N12Compact.FullAuxWallPositiveLeftNeighbor
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds
set_option Elab.async false

private theorem cosine_small {l r : ℝ} (ln : Normal l r) (small : r≤3/10) :
    19/20≤l := by
  have bounds := normal_bounds ln
  have square := mul_nonneg (sub_nonneg.mpr small)
    (show 0≤3/10+r by linarith only [ln.1])
  apply le_of_not_gt
  intro wrong
  have other := mul_nonneg (sub_nonneg.mpr wrong.le)
    (show 0≤19/20+l by linarith only [bounds.1])
  nlinarith only [square,other,ln.2.2]

private theorem diagonal {l r u : ℝ} (ln : Normal l r)
    (large : 4/25≤r) (small : r≤3/10) (offset : u≤1/1000) :
    0<l*(2-2*l-u)-(457/500)*r^2 := by
  have bounds := normal_bounds ln
  have cosine := cosine_small ln small
  have square := mul_nonneg (sub_nonneg.mpr large)
    (show 0≤r+4/25 by linarith only [ln.1])
  have coefficient := mul_nonneg (sq_nonneg r)
    (show 0≤(543/500)*l-(457/500)-1177/10000 by linarith only [cosine])
  have product := mul_nonneg (sub_nonneg.mpr bounds.2.1)
    (show 0≤l+2 by linarith only [bounds.1])
  have width := mul_nonneg
    (show 0≤l*(1+l) by nlinarith only [bounds.1,sq_nonneg l])
    (sub_nonneg.mpr offset)
  have identity :
      (1+l)*(l*(2-2*l-u)-(457/500)*r^2)=
      r^2*((543/500)*l-(457/500))-l*(1+l)*u := by
    linear_combination (-2*l)*ln.2.2
  have scaled : 0<(1+l)*(l*(2-2*l-u)-(457/500)*r^2) := by
    nlinarith only [identity,square,coefficient,product,width]
  exact pos_of_mul_pos_right scaled (by linarith only [bounds.1])

theorem below {C S l r u : ℝ} (dn : Normal C S) (ln : Normal l r)
    (small : S≤11/50) (large : 4/25≤r) (offset : u≤1/1000)
    (order : r≤S) :
    0<l*(1+(l*C+r*S)-2*C-u)-(457/500)*S*r := by
  have lb := normal_bounds ln
  have cosine := cosine_small ln (by linarith only [order,small])
  have diagonal := diagonal ln large (by linarith only [order,small]) offset
  have co := cosine_order dn ln order
  have first := mul_nonneg (sub_nonneg.mpr co)
    (mul_nonneg (show 0≤l by linarith only [lb.1])
      (show 0≤2-l by linarith only [lb.2.1]))
  have second := mul_nonneg (sub_nonneg.mpr order)
    (mul_nonneg ln.1 (show 0≤l-457/500 by linarith only [cosine]))
  have identity :
      (l*(1+(l*C+r*S)-2*C-u)-(457/500)*S*r)-
        (l*(2-2*l-u)-(457/500)*r^2)=
      l*(2-l)*(l-C)+(l-457/500)*r*(S-r) := by
    linear_combination l*ln.2.2
  nlinarith only [diagonal,identity,first,second]

theorem above {C S l r u : ℝ} (dn : Normal C S) (ln : Normal l r)
    (small : S≤11/50) (large : 4/25≤r) (offset : u≤1/1000)
    (order : S≤r) :
    0<l*(1+(l*C+r*S)+(r*C-l*S)-2*C-u)-(457/500)*S*r := by
  have db := normal_bounds dn
  have lb := normal_bounds ln
  have cp : 0<C := by linarith only [db.1]
  have lp : 0<l := by linarith only [lb.1]
  by_cases shallow : r≤3/10
  · have diag := diagonal ln large shallow offset
    have cosine := cosine_order ln dn order
    have first := mul_nonneg (sub_nonneg.mpr order)
      (show 0≤C+l-r-S by linarith only [dn.2.1,ln.2.1])
    have identity0 : (C+l)*(r-S-(C-l))=(r-S)*(C+l-r-S) := by
      linear_combination -dn.2.2+ln.2.2
    have scaled : 0≤(C+l)*(r-S-(C-l)) := by linarith only [first,identity0]
    have gap := nonneg_of_mul_nonneg_right scaled (by linarith only [cp,lp])
    have second := mul_nonneg gap
      (mul_nonneg lp.le (show 0≤2-l-r by linarith only [lb.2.2.2.2.2]))
    have arc := mul_nonneg ln.1
      (show 0≤457/500-r by linarith only [shallow])
    have coefficient : 0≤(457/500)*r-2*l*(1-l) := by
      nlinarith only [arc,ln.2.2,sq_nonneg (1-l)]
    have third := mul_nonneg (sub_nonneg.mpr order) coefficient
    have identity :
        (l*(1+(l*C+r*S)+(r*C-l*S)-2*C-u)-(457/500)*S*r)-
          (l*(2-2*l-u)-(457/500)*r^2)=
        l*(2-l-r)*(r-S-(C-l))+
          (r-S)*((457/500)*r-2*l*(1-l)) := by
      linear_combination l*ln.2.2
    nlinarith only [diag,identity,second,third]
  · have lower : 3/10≤r := le_of_lt (lt_of_not_ge shallow)
    have product := mul_nonneg (sub_nonneg.mpr lower)
      (show 0≤l-3/10 by linarith only [ln.2.1,lower])
    have sum : 5/4≤l+r := by
      apply le_of_not_gt
      intro wrong
      have comparison := mul_nonneg (sub_nonneg.mpr wrong.le)
        (show 0≤l+r+13/20 by linarith only [lb.2.2.2.2.1])
      nlinarith only [product,comparison,ln.2.2]
    let K := l*(l-r)+(457/500)*r
    have kp : 0≤K := by
      dsimp [K]
      exact add_nonneg (mul_nonneg lp.le (sub_nonneg.mpr ln.2.1))
        (mul_nonneg (by norm_num) ln.1)
    have kcap : K≤l := by
      have first := mul_nonneg (sub_nonneg.mpr lb.2.1)
        (sub_nonneg.mpr ln.2.1)
      dsimp [K]
      nlinarith only [first,ln.2.2,ln.1]
    have first := mul_nonneg (sub_nonneg.mpr db.2.1)
      (mul_nonneg lp.le (show 0≤2-l-r by linarith only [lb.2.2.2.2.2]))
    have second := mul_nonneg (sub_nonneg.mpr small) kp
    have third := mul_nonneg lp.le (sub_nonneg.mpr offset)
    have fourth := mul_nonneg lp.le (sub_nonneg.mpr sum)
    dsimp [K] at kp kcap second
    nlinarith only [first,second,third,fourth,kcap,lp]

/-- Exclude C's own separator with the actual left square, its container
and marker. Only the original opposite-square displacement is used. -/
theorem impossible (L D : OpenSquare) (ln : Normal L.c L.s) (dn : Normal D.c D.s)
    (side : 1<D.side) (same : L.side=D.side) (box : InsideContainer L)
    (marker : L.Inside (457/500) 2)
    (small : D.s≤11/50) (large : 4/25≤L.s)
    (offset : D.loU+D.side-2*(D.c+D.s)≤1/1000)
    (axis : upper L D.c D.s≤D.loU) : False := by
  have lb := normal_bounds ln
  have db := normal_bounds dn
  have lp : 0<L.c := by linarith only [lb.1]
  have cp : 0<D.c := by linarith only [db.1]
  let alpha := L.c*D.c+L.s*D.s
  let H := L.s*D.c-L.c*D.s
  let u := D.loU+D.side-2*(D.c+D.s)
  have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos lp cp) (mul_nonneg ln.1 dn.1)
  have wall0 := FourSquareBLBridge.left_wall L lp.le box
  rw [abs_of_nonneg ln.1] at wall0
  dsimp [centerX] at wall0
  have wall : L.s*(L.loV+L.side)≤L.c*(L.loU+L.side)-L.c*L.side := by
    nlinarith only [wall0]
  have weightedWall := mul_nonneg ap.le (sub_nonneg.mpr wall)
  have weightedAxis := mul_nonneg lp.le (sub_nonneg.mpr axis)
  have markerWeight := mul_nonneg dn.1 (sub_nonneg.mpr marker.2.2.2.le)
  have cancellation : alpha*L.s-L.c*H=D.s := by
    dsimp [alpha,H]
    linear_combination D.s*ln.2.2
  by_cases sign : 0≤H
  · have formula : upper L D.c D.s=alpha*(L.loU+L.side)-H*L.loV := by
      dsimp [upper,supportRadius,centerX,centerY]
      rw [abs_of_nonneg (show 0≤D.c*L.c+D.s*L.s by dsimp [alpha] at ap; nlinarith only [ap]),
        abs_of_nonpos (show -D.c*L.s+D.s*L.c≤0 by dsimp [H] at sign; nlinarith only [sign])]
      dsimp [alpha,H]; ring
    have order : D.s≤L.s := sine_order ln dn (by dsimp [H] at sign; nlinarith only [sign])
    have margin := above dn ln small large offset order
    have strict := mul_pos (sub_pos.mpr side)
      (mul_pos lp (show 0<1+alpha+H by linarith only [ap,sign]))
    have identity : alpha*(L.c+L.s)-D.s=L.c*(alpha+H) := by
      dsimp [alpha,H]
      linear_combination D.s*ln.2.2
    have cancelV := congrArg (fun z : ℝ => z*L.loV) cancellation
    have cancelSide := congrArg (fun z : ℝ => z*D.side) identity
    rw [same] at weightedWall markerWeight formula
    rw [formula] at weightedAxis
    change 0<L.c*(1+alpha+H-2*D.c-u)-(457/500)*D.s*L.s at margin
    dsimp only [u] at margin
    clear_value alpha H
    nlinarith only [weightedWall,weightedAxis,markerWeight,cancelV,cancelSide,strict,margin]
  · have sign : H≤0 := le_of_lt (lt_of_not_ge sign)
    have formula : upper L D.c D.s=alpha*(L.loU+L.side)-H*(L.loV+L.side) := by
      dsimp [upper,supportRadius,centerX,centerY]
      rw [abs_of_nonneg (show 0≤D.c*L.c+D.s*L.s by dsimp [alpha] at ap; nlinarith only [ap]),
        abs_of_nonneg (show 0≤-D.c*L.s+D.s*L.c by dsimp [H] at sign; nlinarith only [sign])]
      dsimp [alpha,H]; ring
    have order : L.s≤D.s := sine_order dn ln (by dsimp [H] at sign; nlinarith only [sign])
    have margin := below dn ln small large offset order
    have strict := mul_pos (sub_pos.mpr side)
      (mul_pos lp (show 0<1+alpha by linarith only [ap]))
    have cancelV := congrArg (fun z : ℝ => z*(L.loV+L.side)) cancellation
    rw [same] at weightedWall markerWeight formula cancelV
    rw [formula] at weightedAxis
    change 0<L.c*(1+alpha-2*D.c-u)-(457/500)*D.s*L.s at margin
    dsimp only [u] at margin
    clear_value alpha H
    nlinarith only [weightedWall,weightedAxis,markerWeight,formula,cancelV,strict,margin]

#print axioms below
#print axioms above
#print axioms impossible
end N12Compact.FullAuxWallPositiveLeftNeighbor
