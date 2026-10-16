import Compact.Completion.C1092.MPPMCrosspointQuadraticArc

/-! The three full-interval quadratic interpolation margins needed by
G01/G11. The central lower arc uses ten symmetric degree-two Bernstein
coefficients; all are explicit nonnegative products. The other two arcs
need only rational box bounds on the exact symmetric remainder. -/
namespace N12Compact.C1092MPPMCrosspointSupport.QuadraticArc
open C1092ShallowPositiveScalars
set_option Elab.async false
noncomputable section

private def one (a b c A B C : ℝ) : ℝ := A*b*c+a*B*c+a*b*C
private def mixed (a b c A B C x y z : ℝ) : ℝ :=
  a*B*z+a*y*C+A*b*z+A*y*c+x*b*C+x*B*c

/-- The exact central lower-arc remainder for every triple in [0,p].
Its sole endpoint restriction is cosH(p)>=sinH(p), written without
division as 1-2p-p²>=0. No steep lower-angle bound is required. -/
theorem central_remainder (p q z r : ℝ) (pn : 0≤p) (pu : p≤1)
    (diagonal : 0≤1-2*p-p^2)
    (qn : 0≤q) (qp : q≤p) (zn : 0≤z) (zp : z≤p) (rn : 0≤r) (rp : r≤p) :
    0≤remainder (cosH p) (sinH p) (sinH p) q z r := by
  by_cases zero : p=0
  · have q0 : q=0 := by linarith only [qn,qp,zero]
    have z0 : z=0 := by linarith only [zn,zp,zero]
    have r0 : r=0 := by linarith only [rn,rp,zero]
    norm_num [zero,q0,z0,r0,remainder,X,Y,Z,sum3,pair3,triple3,cosH,sinH]
  have pp : 0<p := lt_of_le_of_ne pn (Ne.symm zero)
  have p1 : 0≤1-p := by linarith only [pu]
  have qd : 0≤p-q := sub_nonneg.mpr qp
  have zd : 0≤p-z := sub_nonneg.mpr zp
  have rd : 0≤p-r := sub_nonneg.mpr rp
  let q0 := (p-q)^2
  let q1 := 2*q*(p-q)
  let q2 := q^2
  let z0 := (p-z)^2
  let z1 := 2*z*(p-z)
  let z2 := z^2
  let r0 := (p-r)^2
  let r1 := 2*r*(p-r)
  let r2 := r^2
  have q0n : 0≤q0 := sq_nonneg _
  have q1n : 0≤q1 := by dsimp [q1]; positivity
  have q2n : 0≤q2 := sq_nonneg _
  have z0n : 0≤z0 := sq_nonneg _
  have z1n : 0≤z1 := by dsimp [z1]; positivity
  have z2n : 0≤z2 := sq_nonneg _
  have r0n : 0≤r0 := sq_nonneg _
  have r1n : 0≤r1 := by dsimp [r1]; positivity
  have r2n : 0≤r2 := sq_nonneg _
  let V :=
    (1-2*p-p^2)*q0*z0*r0+
    (1-p)^2*one q0 z0 r0 q1 z1 r1+
    ((1-p)^2*(1+p^2))*one q0 z0 r0 q2 z2 r2+
    ((1-p)^2+(3/2)*p^2+p^4/2)*one q1 z1 r1 q0 z0 r0+
    ((1-p)^2+2*p^2*(1-p+p^2))*mixed q0 z0 r0 q1 z1 r1 q2 z2 r2+
    ((1-p)^2*(1+p^2)^2)*(one q2 z2 r2 q0 z0 r0+one q2 z2 r2 q1 z1 r1)+
    ((1-p)^2+(5/2)*p^2+(3/2)*p^4)*q1*z1*r1+
    ((1-p)^2+p^2/2+2*p^2*(1-p)+3*p^4+p^6/2)*one q1 z1 r1 q2 z2 r2+
    ((1-2*p-p^2)*(1+p^2)^3)*q2*z2*r2
  have Vn : 0≤V := by
    have middle : 0≤1-p+p^2 := add_nonneg p1 (sq_nonneg p)
    dsimp only [V,one,mixed]
    positivity
  have identity : p^6*(1+p^2)*remainder (cosH p) (sinH p) (sinH p) q z r=V := by
    dsimp [remainder,cosH,sinH,X,Y,Z,sum3,pair3,triple3,V,one,mixed,
      q0,q1,q2,z0,z1,z2,r0,r1,r2]
    field_simp [(half_den_pos p).ne']
    <;> ring
  have weighted : 0≤p^6*(1+p^2)*remainder (cosH p) (sinH p) (sinH p) q z r := by
    rw [identity]; exact Vn
  exact nonneg_of_mul_nonneg_right weighted (by positivity)

private structure Box (u q z r : ℝ) : Prop where
  sum_nonnegative : 0≤sum3 q z r
  sum_upper : sum3 q z r≤3*u
  pair_nonnegative : 0≤pair3 q z r
  pair_upper : pair3 q z r≤3*u^2
  triple_nonnegative : 0≤triple3 q z r
  triple_upper : triple3 q z r≤u^3
  Z_lower : 1≤Z q z r
  Z_upper : Z q z r≤(1+u^2)^3

private theorem box (u q z r : ℝ) (un : 0≤u)
    (qn : 0≤q) (qu : q≤u) (zn : 0≤z) (zu : z≤u) (rn : 0≤r) (ru : r≤u) :
    Box u q z r := by
  have qz := mul_le_mul qu zu zn un
  have qr := mul_le_mul qu ru rn un
  have zr := mul_le_mul zu ru rn un
  have triple := mul_le_mul qz ru rn (mul_nonneg un un)
  have qq := mul_le_mul qu qu qn un
  have zz := mul_le_mul zu zu zn un
  have rr := mul_le_mul ru ru rn un
  have qcap : 1+q^2≤1+u^2 := by nlinarith only [qq]
  have zcap : 1+z^2≤1+u^2 := by nlinarith only [zz]
  have rcap : 1+r^2≤1+u^2 := by nlinarith only [rr]
  have upper0 := mul_le_mul qcap zcap (by positivity) (by positivity)
  have upper1 := mul_le_mul upper0 rcap (by positivity) (by positivity)
  have lower0 := mul_le_mul (show (1:ℝ)≤1+q^2 by nlinarith only [sq_nonneg q])
    (show (1:ℝ)≤1+z^2 by nlinarith only [sq_nonneg z]) (by norm_num) (by positivity)
  have lower1 := mul_le_mul lower0
    (show (1:ℝ)≤1+r^2 by nlinarith only [sq_nonneg r]) (by norm_num) (by positivity)
  exact {
    sum_nonnegative := by dsimp [sum3]; positivity
    sum_upper := by dsimp [sum3]; linarith only [qu,zu,ru]
    pair_nonnegative := by dsimp [pair3]; positivity
    pair_upper := by dsimp [pair3]; nlinarith only [qz,qr,zr]
    triple_nonnegative := by dsimp [triple3]; positivity
    triple_upper := by dsimp [triple3]; nlinarith only [triple]
    Z_lower := by dsimp [Z]; nlinarith only [lower1]
    Z_upper := by dsimp [Z]; nlinarith only [upper1] }

private theorem X_lower (u q z r : ℝ) (un : 0≤u) (b : Box u q z r) :
    1-(3*u)^2-(3*u^2)^2≤X q z r := by
  have first := mul_le_mul b.sum_upper b.sum_upper b.sum_nonnegative (by positivity)
  have last := mul_le_mul b.pair_upper b.pair_upper b.pair_nonnegative (by positivity)
  dsimp [X]
  nlinarith only [first,last,sq_nonneg (triple3 q z r)]

/-- The beta>=p lower-quadrant G01 piece. The broad rational box
[1/3,1/2] already gives a strictly positive remainder. -/
theorem middle_remainder (a b C q z r : ℝ)
    (an : 0≤a) (au : a≤1/5) (bl : 7/5≤b) (Cn : 0≤C) (Cu : C≤71/100)
    (ql : 1/3≤q) (qu : q≤1/2) (zl : 1/3≤z) (zu : z≤1/2)
    (rl : 1/3≤r) (ru : r≤1/2) : 0≤remainder a b C q z r := by
  have data := box (1/2) q z r (by norm_num)
    (by linarith only [ql]) qu (by linarith only [zl]) zu (by linarith only [rl]) ru
  have Xlow : -29/16≤X q z r := by
    have h := X_lower (1/2) q z r (by norm_num) data
    norm_num at h; simpa only [neg_div] using h
  have cap := mul_le_mul data.triple_upper data.pair_upper data.pair_nonnegative (by norm_num)
  have Ylow : 29/32≤Y q z r := by
    dsimp [Y,sum3] at *
    nlinarith only [cap,ql,zl,rl]
  have Zcap : Z q z r≤125/64 := by
    have bound := data.Z_upper
    norm_num at bound
    exact bound
  have first := mul_nonneg an (show 0≤X q z r+29/16 by linarith only [Xlow])
  have middle := mul_nonneg (show 0≤b-7/5 by linarith only [bl])
    (show 0≤Y q z r by linarith only [Ylow])
  have last := mul_nonneg Cn (show 0≤125/64-Z q z r by linarith only [Zcap])
  dsimp [remainder]
  nlinarith only [first,middle,last,au,Ylow,Cu]

/-- After interchanging the boundary coordinates, the upper-quadrant
G11 piece has a negative constant and this uniform positive remainder. -/
theorem upper_remainder (a b q z r : ℝ)
    (an : 0≤a) (au : a≤731/1000) (bl : -171/500≤b) (bu : b≤0)
    (qn : 0≤q) (qu : q≤5/12) (zn : 0≤z) (zu : z≤5/12) (rn : 0≤r) (ru : r≤5/12) :
    0≤remainder a b (-1543/1000) q z r := by
  have data := box (5/12) q z r (by norm_num) qn qu zn zu rn ru
  have Xlow : -1921/2304≤X q z r := by
    have h := X_lower (5/12) q z r (by norm_num) data
    norm_num at h; simpa only [neg_div] using h
  have product := mul_nonneg data.triple_nonnegative data.pair_nonnegative
  have Ycap : Y q z r≤5/4 := by
    dsimp [Y]
    nlinarith only [product,data.sum_upper]
  have first := mul_nonneg an (show 0≤X q z r+1921/2304 by linarith only [Xlow])
  have last := mul_nonneg (neg_nonneg.mpr bu) (show 0≤5/4-Y q z r by linarith only [Ycap])
  dsimp [remainder]
  nlinarith only [first,last,au,bl,data.Z_lower]

end
end N12Compact.C1092MPPMCrosspointSupport.QuadraticArc
