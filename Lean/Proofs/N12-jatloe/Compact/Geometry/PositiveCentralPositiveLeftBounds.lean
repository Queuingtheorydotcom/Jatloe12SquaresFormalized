import Compact.Geometry.PositiveCentralEscapeLeft

/-! A continuous positive-left support margin in the missing-west sector.
The true upper-left central vertex, rather than a replacement point,
enters the inequality. A disk estimate covers all canonical left angles. -/
namespace N12Compact.PositiveCentralPositiveLeftBounds

open C977CornerCubic C977CornerSectorBounds PositiveCentralEscapeOrder

noncomputable def vertexDefect (c s : ℝ) : ℝ := (1-c)*(1-s)/c

private theorem defect_bound {c s : ℝ} (normal : Normal c s)
    (wide : 4/5≤c) : 3*(1-c)≤s := by
  have b := normal_bounds normal
  have product := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤10*c-8 by linarith only [wide])
  by_contra no
  have positive := mul_pos (show 0<3*(1-c)-s by linarith only [no])
    (show 0<3*(1-c)+s by linarith only [no,normal.1])
  nlinarith only [positive,product,normal.2.2]

/-- The exact vertex defect increases throughout the required central
sector. This divided-difference identity avoids differentiation. -/
theorem defect_order {p q C S : ℝ} (on : Normal p q) (an : Normal C S)
    (order : q≤S) (wide : 4/5≤C) (small : S≤3/5) :
    vertexDefect p q≤vertexDefect C S := by
  have ob := normal_bounds on
  have ab := normal_bounds an
  have cosine := cosine_order an on order
  have pp : 0<p := by linarith only [wide,cosine]
  have cp : 0<C := by linarith only [wide]
  have op := defect_bound on (le_trans wide cosine)
  have ap := defect_bound an wide
  have product := mul_nonneg (sub_nonneg.mpr ob.2.1) (sub_nonneg.mpr ab.2.1)
  have upper : p*C≤1 := by
    have first := mul_nonneg pp.le (sub_nonneg.mpr ab.2.1)
    nlinarith only [first,ob.2.1]
  have loss := mul_nonneg
    (show 0≤2-p-C by linarith only [ob.2.1,ab.2.1])
    (sub_nonneg.mpr upper)
  have firstAngle := mul_nonneg on.1 (sub_nonneg.mpr small)
  have secondAngle := mul_nonneg an.1
    (show 0≤3/5-q by linarith only [order,small])
  have bracket : 0≤p*C*(p+C-1)-(1-S)*(1-q) := by
    nlinarith only [product,loss,op,ap,firstAngle,secondAngle,on.1,an.1]
  have weighted := mul_nonneg (sub_nonneg.mpr order) bracket
  have polynomial :
      (p+C)*(p*(1-C)*(1-S)-C*(1-p)*(1-q))=
        (S-q)*(p*C*(p+C-1)-(1-S)*(1-q)) := by
    linear_combination (1-S)*on.2.2-(1-q)*an.2.2
  have identity :
      p*C*(p+C)*(vertexDefect C S-vertexDefect p q)=
        (S-q)*(p*C*(p+C-1)-(1-S)*(1-q)) := by
    calc
      _ = (p+C)*(p*(1-C)*(1-S)-C*(1-p)*(1-q)) := by
        dsimp [vertexDefect]
        field_simp [ne_of_gt pp,ne_of_gt cp]
      _ = _ := polynomial
  have scaled : 0≤p*C*(p+C)*(vertexDefect C S-vertexDefect p q) := by
    rw [identity]
    exact weighted
  have gap := nonneg_of_mul_nonneg_right scaled
    (mul_pos (mul_pos pp cp) (add_pos pp cp))
  linarith only [gap]

private theorem reduced_margin {p q l r : ℝ}
    (on : Normal p q) (ln : Normal l r) (shallow : 9/10≤p) :
    0≤(1-l)+r*(l-2+(B p q+q*r)/p)+
      l*(vertexDefect p q+q*(1-p))+r*q*(1-p) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have pp : 0<p := by linarith only [shallow]
  have lp : 0≤l := by linarith only [lb.1]
  let δ := 1-p
  let k : ℝ := 2/7
  let A := 1-q*δ
  let D := q*(p+1/p)-δ/p
  let K := p*l+q*r
  have δp : 0≤δ := sub_nonneg.mpr ob.2.1
  have δu : δ≤1/10 := by dsimp [δ]; linarith only [shallow]
  have qhalf : q≤1/2 := by
    have square := mul_nonneg (sub_nonneg.mpr shallow)
      (show 0≤p+9/10 by linarith only [shallow])
    by_contra no
    have bad := mul_pos (show 0<q-1/2 by linarith only [no])
      (show 0<q+1/2 by linarith only [on.1])
    nlinarith only [square,bad,on.2.2]
  have δq : δ≤q := by dsimp [δ]; linarith only [ob.2.2.2.2.1]
  have reciprocal : 1/p≤10/9 := by
    apply (div_le_iff₀ pp).mpr
    linarith only [shallow]
  have radial : 2≤p+1/p := by
    have identity : p*(p+1/p-2)=(p-1)^2 := by
      field_simp [ne_of_gt pp]
      ring
    have scaled : 0≤p*(p+1/p-2) := by rw [identity]; exact sq_nonneg (p-1)
    have gap := nonneg_of_mul_nonneg_right scaled pp
    linarith only [gap]
  have ap : 0≤A := by
    have product := mul_nonneg on.1 (sub_nonneg.mpr δu)
    dsimp [A]
    clear_value δ
    nlinarith only [product,qhalf]
  have au : A≤1 := by
    dsimp [A]; nlinarith only [mul_nonneg on.1 δp]
  have dp : 0≤D := by
    have identity : p*D=q*(p^2+1)-δ := by
      dsimp [D]
      field_simp [ne_of_gt pp]
    have product := mul_nonneg on.1 (sq_nonneg p)
    have scaled : 0≤p*D := by nlinarith only [identity,product,δq]
    exact nonneg_of_mul_nonneg_right scaled pp
  have du : D≤(19/9)*q := by
    have first := mul_nonneg on.1
      (show 0≤19/9-(p+1/p) by linarith only [ob.2.1,reciprocal])
    have second := div_nonneg δp pp.le
    dsimp [D]; nlinarith only [first,second]
  have aSquare := mul_nonneg ap (sub_nonneg.mpr au)
  have dSquare := mul_nonneg (sub_nonneg.mpr du)
    (show 0≤(19/9)*q+D by clear_value D; linarith only [on.1,dp])
  have qSquare : q^2≤2*δ := by
    dsimp [δ]
    nlinarith only [on.2.2,sq_nonneg (p-1)]
  have norm : A^2+D^2-1≤9*δ := by
    clear_value A D δ
    nlinarith only [aSquare,au,dSquare,qSquare,δp]
  have directionIdentity : p*A+q*D-1=δ*(p^2+(p+1/p)*(1-q)) := by
    dsimp [A,D,δ]
    field_simp [ne_of_gt pp]
    linear_combination (p^2+1)*on.2.2
  have radialWeight := mul_nonneg (sub_nonneg.mpr radial)
    (show 0≤1-q by linarith only [qhalf])
  have pSquare := mul_nonneg (sub_nonneg.mpr shallow)
    (show 0≤p+9/10 by linarith only [shallow])
  have directionBound : 7/4≤p^2+(p+1/p)*(1-q) := by
    nlinarith only [radialWeight,pSquare,qhalf]
  have direction := mul_nonneg δp (sub_nonneg.mpr directionBound)
  have dotBound : (7/4)*δ≤p*A+q*D-1 := by
    nlinarith only [direction,directionIdentity]
  have dotWeight := mul_nonneg (mul_nonneg (show 0≤2*k by norm_num [k]) δp)
    (sub_nonneg.mpr dotBound)
  have normWeight := mul_nonneg (sq_nonneg δ) (sub_nonneg.mpr norm)
  have remainder := mul_nonneg (sq_nonneg δ)
    (show 0≤1-9*δ by clear_value δ; linarith only [δu])
  have diskIdentity :
      (k-δ)^2-((k*p-δ*A)^2+(k*q-δ*D)^2)=
        2*k*δ*(p*A+q*D-1)+δ^2*(1-A^2-D^2) := by
    linear_combination -k^2*on.2.2
  have disk : (k*p-δ*A)^2+(k*q-δ*D)^2≤(k-δ)^2 := by
    dsimp [k] at dotWeight diskIdentity ⊢
    clear_value A D δ
    nlinarith only [diskIdentity,dotWeight,normWeight,remainder]
  have rotation :
      (l*(k*p-δ*A)+r*(k*q-δ*D))^2+
        (r*(k*p-δ*A)-l*(k*q-δ*D))^2=
      (k*p-δ*A)^2+(k*q-δ*D)^2 := by
    linear_combination ((k*p-δ*A)^2+(k*q-δ*D)^2)*ln.2.2
  have radius : 0<k-δ := by dsimp [k]; linarith only [δu]
  have dot : l*(k*p-δ*A)+r*(k*q-δ*D)≤k-δ := by
    apply le_of_not_gt
    intro no
    clear_value k δ A D
    have bad := mul_pos
      (show 0<l*(k*p-δ*A)+r*(k*q-δ*D)-(k-δ) by linarith only [no])
      (show 0<l*(k*p-δ*A)+r*(k*q-δ*D)+(k-δ) by linarith only [no,radius])
    nlinarith only [bad,disk,rotation,
      sq_nonneg (r*(k*p-δ*A)-l*(k*q-δ*D))]
  have rupper : r≤5/7 := by linarith only [ln.2.1,lb.2.2.2.2.2]
  have normalDot := dot_le_one on ln
  have correction := mul_nonneg
    (show 0≤1-r-k by dsimp [k]; linarith only [rupper])
    (show 0≤1-K by dsimp [K]; linarith only [normalDot])
  have identity :
      p*((1-l)+r*(l-2+(B p q+q*r)/p)+
        l*(vertexDefect p q+q*(1-p))+r*q*(1-p))=
      (1-r)*(1-K)+δ*(-1+A*l+D*r) := by
    dsimp [B,vertexDefect,K,δ,A,D]
    field_simp [ne_of_gt pp]
    linear_combination (-r)*on.2.2
  have scaled : 0≤p*((1-l)+r*(l-2+(B p q+q*r)/p)+
      l*(vertexDefect p q+q*(1-p))+r*q*(1-p)) := by
    dsimp [K] at identity correction
    clear_value A D δ k
    nlinarith only [identity,correction,dot]
  exact nonneg_of_mul_nonneg_right scaled pp

/-- The upper-left vertex cannot lie beyond positive L's U face when
L is above O on O's V axis. The central angle is removed monotonically. -/
theorem own_axis_margin {p q C S l r : ℝ}
    (on : Normal p q) (an : Normal C S) (ln : Normal l r)
    (order : q≤S) (shallow : 9/10≤p) (wide : 4/5≤C) (small : S≤3/5) :
    0≤(1-l)+r*(l-2+(B p q+q*r)/p)+
      l*(vertexDefect C S+S*(1-p))+r*S*(1-C) := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have cosine := cosine_order an on order
  have lp : 0≤l := by linarith only [lb.1]
  have base := reduced_margin on ln shallow
  have change := defect_order on an order wide small
  have first := mul_nonneg lp (sub_nonneg.mpr change)
  have second := mul_nonneg lp
    (mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr ob.2.1))
  have third := mul_nonneg ln.1
    (mul_nonneg (sub_nonneg.mpr order) (sub_nonneg.mpr ob.2.1))
  have fourth := mul_nonneg (mul_nonneg ln.1 an.1) (sub_nonneg.mpr cosine)
  nlinarith only [base,first,second,third,fourth]

#print axioms defect_order
#print axioms own_axis_margin
end N12Compact.PositiveCentralPositiveLeftBounds
