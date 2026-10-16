import Compact.Geometry.CornerWallCycleBounds

/-! Genuine-marker scalar for O-v / L-v when positive L tilts no
farther than O. The wall face is weakened to t+3d, while the true bottom
marker coefficient 457/500 is retained. Source only, uncompiled. -/
namespace N12Compact.CornerWallMarkerMixedBounds

open C977CornerCubic C977CornerSectorBounds

noncomputable def boundary (c s : ℝ) : ℝ :=
  1+s/c-2*s-(457/500)*s^2/c

noncomputable def G (c s : ℝ) : ℝ := (boundary c s+s)/c

theorem g_order {c s d t : ℝ}
    (on : Normal c s) (wn : Normal d t) (order : s≤t)
    (small : t≤3/5) (wide : 4/5≤d) : G d t≤G c s := by
  have ob := normal_bounds on
  have wb := normal_bounds wn
  have dc := cosine_order wn on order
  have cp : 0<c := by linarith only [wide,dc]
  have dp : 0<d := by linarith only [wide]
  by_cases zero : t=0
  · have sz : s=0 := by linarith only [on.1,order,zero]
    have ce : c=1 := by nlinarith only [on.2.2,sz,cp]
    have de : d=1 := by nlinarith only [wn.2.2,zero,dp]
    simp only [zero,sz,ce,de,le_refl]
  · have tp : 0<t := lt_of_le_of_ne wn.1 (Ne.symm zero)
    have up : 0<s+t := by linarith only [on.1,tp]
    have vp : 0<c+d := add_pos cp dp
    have dp1 : 0<1+d := by linarith only [dp]
    let K := (c*d/(c+d))*(1-s)+((1-d)+d*s^2+s*t)/(s+t)
    let J := (d+s+t^2*(1-s^2)/(s+t))/(1+d)
    have ratio : c*d/(c+d)≤d/(1+d) := by
      apply (div_le_div_iff₀ vp dp1).2
      have product := mul_nonneg (sq_nonneg d) (sub_nonneg.mpr ob.2.1)
      nlinarith only [product]
    have ratioWeighted := mul_nonneg
      (show 0≤1-s by linarith only [order,small]) (sub_nonneg.mpr ratio)
    have relation : J =
        (d/(1+d))*(1-s)+((1-d)+d*s^2+s*t)/(s+t) := by
      dsimp [J]
      field_simp [ne_of_gt up,ne_of_gt dp1]
      linear_combination (1-s^2)*wn.2.2
    have comparison : K≤J := by
      dsimp [K]
      nlinarith only [relation,ratioWeighted]
    have product := mul_nonneg
      (mul_nonneg (show 0≤1-t^2 by nlinarith only [wn.2.2,sq_nonneg d])
        (sub_nonneg.mpr order))
      (show 0≤t+2*s by linarith only [tp,on.1])
    have shape :
        2*(s+t)*((3*t-t^3)/2-(s+t^2*(1-s^2)/(s+t))) =
          (1-t^2)*(t-s)*(t+2*s) := by
      field_simp [ne_of_gt up]
      ring
    have shapeBound : s+t^2*(1-s^2)/(s+t)≤(3*t-t^3)/2 := by
      have scaled : 0≤2*(s+t)*((3*t-t^3)/2-(s+t^2*(1-s^2)/(s+t))) := by
        nlinarith only [shape,product]
      have unscaled := nonneg_of_mul_nonneg_right scaled
        (show 0<2*(s+t) by linarith only [up])
      linarith only [unscaled]
    have cubicFactor : 0≤(3/5-t)*(66/25-(3/5)*t-t^2) := by
      have range := mul_nonneg wn.1 (sub_nonneg.mpr small)
      have bracket : 0≤66/25-(3/5)*t-t^2 := by
        nlinarith only [small,range]
      exact mul_nonneg (sub_nonneg.mpr small) bracket
    have cubic : (3*t-t^3)/2≤99/125 := by
      nlinarith only [cubicFactor]
    have jbound : J≤9/10 := by
      have numerator : d+s+t^2*(1-s^2)/(s+t)≤(9/10)*(1+d) := by
        linarith only [shapeBound,cubic,wb.2.1]
      dsimp [J]
      exact (div_le_iff₀ dp1).2 numerator
    have kbound : K≤9/10 := le_trans comparison jbound
    have linear : d^2*s-c^2*t=-(t-s)*(1+s*t) := by
      linear_combination s*wn.2.2-t*on.2.2
    have quadratic : c^2*t^2-d^2*s^2=t^2-s^2 := by
      linear_combination t^2*on.2.2-s^2*wn.2.2
    have cosine : c-d=(t-s)*(s+t)/(c+d) := by
      apply (eq_div_iff (ne_of_gt vp)).2
      linear_combination on.2.2-wn.2.2
    have expansion : c^2*d^2*(G c s-G d t)=
        (t-s)*((457/500)*(s+t)-(1-d)-d*s^2-s*t)-
          c*d*(1-s)*(c-d) := by
      calc
        _ = c*d*(c*(t-s)-(1-s)*(c-d))+(d^2*s-c^2*t)+
            (457/500)*(c^2*t^2-d^2*s^2) := by
          dsimp [G,boundary]
          field_simp [ne_of_gt cp,ne_of_gt dp]
          ring
        _ = _ := by
          rw [linear,quadratic]
          linear_combination d*(t-s)*on.2.2
    have identity :
        c^2*d^2*(G c s-G d t) = (t-s)*(s+t)*((457/500)-K) := by
      rw [expansion,cosine]
      dsimp [K]
      field_simp [ne_of_gt up,ne_of_gt vp]
      ring
    have positive := mul_nonneg
      (mul_nonneg (sub_nonneg.mpr order) up.le)
      (show 0≤457/500-K by linarith only [kbound])
    have scaled : 0≤c^2*d^2*(G c s-G d t) := by
      nlinarith only [identity,positive]
    have unscaled := nonneg_of_mul_nonneg_right scaled
      (mul_pos (sq_pos_of_pos cp) (sq_pos_of_pos dp))
    linarith only [unscaled]

theorem g_upper {c s : ℝ} (on : Normal c s) (small : s≤3/5) : G c s≤1 := by
  have ob := normal_bounds on
  have cp : 0<c := by linarith only [ob.1]
  have factor := mul_nonneg (sub_nonneg.mpr ob.2.1)
    (show 0≤1-s-(43/500)*(1+c) by linarith only [small,ob.2.1])
  have identity :
      c^2*(G c s-1)=-(1-c)*(1-s-(43/500)*(1+c)) := by
    dsimp [G,boundary]
    field_simp [ne_of_gt cp]
    linear_combination -457*on.2.2
  have scaled : c^2*(G c s-1)≤0 := by nlinarith only [identity,factor]
  have unscaled := nonpos_of_mul_nonpos_right scaled (sq_pos_of_pos cp)
  linarith only [unscaled]

theorem endpoint_gain {d t : ℝ} (wn : Normal d t)
    (small : t≤3/5) (wide : 4/5≤d) :
    2+(4/7)*(1-d)^2≤G d t+t+(1-t)/d := by
  have wb := normal_bounds wn
  have dp : 0<d := by linarith only [wide]
  let z := 1-d
  have zp : 0≤z := by dsimp [z]; linarith only [wb.2.1]
  have zu : z≤1/5 := by dsimp [z]; linarith only [wide]
  have lower : 3*z≤t := by
    have product := mul_nonneg zp
      (show 0≤10*d-8 by linarith only [wide])
    by_contra no
    have positive := mul_pos (show 0<3*z-t by linarith only [no])
      (show 0<3*z+t by linarith only [no,wn.1])
    dsimp [z] at positive product
    nlinarith only [positive,product,wn.2.2]
  let F := (543/500+4/7)*z-(3+2*(4/7))*z^2+(4/7)*z^3
  let Fmax : ℝ := (543/500+4/7)*(1/5)-(3+2*(4/7))*(1/5)^2+(4/7)*(1/5)^3
  have bracket : 0≤543/500+4/7-(3+2*(4/7))*(1/5+z)+
      (4/7)*((1/5)^2+(1/5)*z+z^2) := by
    have square := sq_nonneg z
    nlinarith only [zu,zp,square]
  have product := mul_nonneg (sub_nonneg.mpr zu) bracket
  have factor : Fmax-F=(1/5-z)*
      (543/500+4/7-(3+2*(4/7))*(1/5+z)+
        (4/7)*((1/5)^2+(1/5)*z+z^2)) := by
    dsimp [F,Fmax]
    ring
  have fbound : F≤43/250 := by
    have bound : Fmax≤43/250 := by dsimp [Fmax]; norm_num
    nlinarith only [bound,factor,product]
  have orderProduct := mul_nonneg zp (sub_nonneg.mpr lower)
  have orderIdentity :
      F-z*(543/500-t+(4/7)*d^2)=z*(t-3*z) := by
    dsimp [F,z]
    ring
  have response : 0≤43/250-z*(543/500-t+(4/7)*d^2) := by
    clear_value F Fmax z
    nlinarith only [fbound,orderProduct,orderIdentity]
  have numerator := mul_nonneg zp response
  have identity :
      d^2*(G d t+t+(1-t)/d-2-(4/7)*(1-d)^2) =
        z*(43/250-z*(543/500-t+(4/7)*d^2)) := by
    dsimp [G,boundary,z]
    field_simp [ne_of_gt dp]
    linear_combination -799750*wn.2.2
  have scaled : 0≤d^2*(G d t+t+(1-t)/d-2-(4/7)*(1-d)^2) := by
    nlinarith only [identity,numerator]
  have unscaled := nonneg_of_mul_nonneg_right scaled (sq_pos_of_pos dp)
  linarith only [unscaled]

theorem norm {c s d t : ℝ}
    (on : Normal c s) (wn : Normal d t) (order : s≤t)
    (small : t≤3/5) (wide : 4/5≤d) :
    (G c s+t+(1-t)/d-3)^2+(1-d)^2≤1 := by
  have wb := normal_bounds wn
  have dp : 0<d := by linarith only [wide]
  have monotone := g_order on wn order small wide
  have endpoint := endpoint_gain wn small wide
  have gu := g_upper on (le_trans order small)
  let P := G c s+t+(1-t)/d-3
  let z := 1-d
  have zp : 0≤z := by dsimp [z]; linarith only [wb.2.1]
  have zu : z≤1/5 := by dsimp [z]; linarith only [wide]
  have zs : z^2≤1/25 := by clear_value z; nlinarith only [zu,zp]
  have lower : -1+(4/7)*z^2≤P := by
    dsimp [P,z]
    linarith only [monotone,endpoint]
  have inverse : (1-t)/d≤5/4 := by
    apply (div_le_iff₀ dp).2
    linarith only [wide,wn.1]
  have upper : P≤0 := by
    dsimp [P]
    linarith only [gu,inverse,small]
  change P^2+z^2≤1
  clear_value P z
  have squareProduct := mul_nonneg (sub_nonneg.mpr lower)
    (show 0≤1-(4/7)*z^2-P by linarith only [zs,upper])
  have correction := mul_nonneg (sq_nonneg z)
    (show 0≤2*(4/7)-1-(4/7)^2*z^2 by linarith only [zs])
  have result : P^2+z^2≤1 := by
    nlinarith only [squareProduct,correction]
  exact result

theorem linear_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (small : t≤3/5) (wide : 4/5≤d) :
    0≤1+l*(G c s+t+(1-t)/d-3)-r*(1-d) := by
  let P := G c s+t+(1-t)/d-3
  have normBound := norm on wn order small wide
  have rotation : (l*P-r*(1-d))^2+(r*P+l*(1-d))^2=P^2+(1-d)^2 := by
    linear_combination (P^2+(1-d)^2)*ln.2.2
  have squared : (l*P-r*(1-d))^2≤1 := by
    change P^2+(1-d)^2≤1 at normBound
    nlinarith only [normBound,rotation,sq_nonneg (r*P+l*(1-d))]
  have disk : 0≤1+l*P-r*(1-d) := by
    nlinarith only [squared,sq_nonneg (1+l*P-r*(1-d))]
  exact disk

theorem low_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (leftOrder : r≤s) (small : t≤3/5) (wide : 4/5≤d) :
    0≤1+(l/c)*boundary c s+(s*l-c*r)*(l+r)/c+
      r*d+l*t+l/d-3*l-l*t/d := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have cp : 0<c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [wide]
  have cl := cosine_order on ln leftOrder
  have first := mul_nonneg cp.le (sub_nonneg.mpr leftOrder)
  have second := mul_nonneg on.1 (sub_nonneg.mpr cl)
  have cross : 0≤s*l-c*r := by nlinarith only [first,second]
  have extra := mul_nonneg (div_nonneg cross cp.le)
    (show 0≤l+r-1 by linarith only [lb.2.2.2.2.1])
  let P := G c s+t+(1-t)/d-3
  have disk := linear_margin on wn ln order small wide
  have identity :
      (1+(l/c)*boundary c s+(s*l-c*r)*(l+r)/c+
        r*d+l*t+l/d-3*l-l*t/d)-
      (1+l*P-r*(1-d))=((s*l-c*r)/c)*(l+r-1) := by
    dsimp [P,G]
    field_simp [ne_of_gt cp,ne_of_gt dp]
    ring
  nlinarith only [disk,identity,extra]

/-- The original strict left marker supplies the upper-U corner needed
when L tilts farther than O. Its 43/500 horizontal offset exceeds the
entire canonical corner defect (at most 1/12). -/
theorem high_margin {c s d t l r : ℝ}
    (on : Normal c s) (wn : Normal d t) (ln : Normal l r)
    (order : s≤t) (leftOrder : s≤r) (small : t≤3/5) (wide : 4/5≤d) :
    0≤(boundary c s-(c*r-s*l)*((457/500)*l+r))/(c*l+s*r)+
      1+r*d+l*t+l/d-3*l-l*t/d := by
  have ob := normal_bounds on
  have lb := normal_bounds ln
  have dc := cosine_order wn on order
  have cp : 0<c := by linarith only [wide,dc]
  have dp : 0<d := by linarith only [wide]
  have lp : 0<l := by linarith only [lb.1]
  have lc := cosine_order ln on leftOrder
  let D := c*r-s*l
  let K := c*l+s*r
  let v := c-s-boundary c s
  have kp : 0<K := by
    have first := mul_pos cp lp
    have second := mul_nonneg on.1 ln.1
    dsimp [K]
    linarith only [first,second]
  have first := mul_nonneg cp.le (sub_nonneg.mpr leftOrder)
  have second := mul_nonneg on.1 (sub_nonneg.mpr lc)
  have cross : 0≤D := by dsimp [D]; nlinarith only [first,second]
  have defect : 3*(1-c)≤s := by
    have product := mul_nonneg (sub_nonneg.mpr ob.2.1)
      (show 0≤10*c-8 by linarith only [wide,dc])
    by_contra no
    have positive := mul_pos (show 0<3*(1-c)-s by linarith only [no])
      (show 0<3*(1-c)+s by linarith only [no,on.1])
    nlinarith only [positive,product,on.2.2]
  have multiplied := mul_nonneg
    (show 0≤1-s by linarith only [order,small]) (sub_nonneg.mpr defect)
  have defectBound : (1-c)*(1-s)≤1/12 := by
    nlinarith only [multiplied,sq_nonneg (2*s-1)]
  have vIdentity : c*v=(1-c)*(1-s)-(43/500)*s^2 := by
    dsimp [v,boundary]
    field_simp [ne_of_gt cp]
    linear_combination 500*on.2.2
  have vBound : v≤(43/500)*c := by
    have scaled : 0≤c*((43/500)*c-v) := by
      nlinarith only [vIdentity,on.2.2,defectBound]
    have unscaled := nonneg_of_mul_nonneg_right scaled cp
    linarith only [unscaled]
  have firstProduct := mul_nonneg (sub_nonneg.mpr ln.2.1)
    (show 0≤(43/500)*c by linarith only [cp])
  have secondProduct := mul_nonneg ln.1 (sub_nonneg.mpr vBound)
  have bracket : 0≤(43/500)*c*l-r*v := by
    nlinarith only [firstProduct,secondProduct]
  have gain := mul_nonneg cross bracket
  have frameRelation : c-l*K=r*D := by
    dsimp [K,D]
    linear_combination -c*ln.2.2
  have identity :
      c*K*((boundary c s-D*((457/500)*l+r))/K+
        1+r*d+l*t+l/d-3*l-l*t/d-
        (1+l*(G c s+t+(1-t)/d-3)-r*(1-d))) =
          D*((43/500)*c*l-r*v) := by
    calc
      _ = (c-l*K)*boundary c s+D*(K-c*((457/500)*l+r)) := by
        dsimp [G]
        field_simp [ne_of_gt cp,ne_of_gt dp,ne_of_gt kp]
        dsimp [D,K]
        ring
      _ = _ := by
        rw [frameRelation]
        dsimp [K,v]
        ring
  have disk := linear_margin on wn ln order small wide
  have scaled : 0≤c*K*((boundary c s-D*((457/500)*l+r))/K+
        1+r*d+l*t+l/d-3*l-l*t/d) := by
    have weight := mul_nonneg (mul_nonneg cp.le kp.le) disk
    nlinarith only [identity,gain,weight]
  have result := nonneg_of_mul_nonneg_right scaled (mul_pos cp kp)
  exact result

end N12Compact.CornerWallMarkerMixedBounds
