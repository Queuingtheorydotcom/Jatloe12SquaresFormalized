import Compact.Geometry.UpperRightNegativeTopBounds
import Compact.Geometry.UpperRightCornerLongitudinal
import Compact.Geometry.C977NegativeCorner

/-! The farther northeast corner point for a positive corner and a
negative top square. Both complete squares and both actual top walls are
retained. The foreign C-wing and unused northeast marker are essential. -/
namespace N12Compact.UpperRightNegativeTopReach

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner UpperRightNegativeTopBounds

theorem top_wall (T : OpenSquare) (s : ℝ) (sign : T.s=-s)
    (box : InsideContainer T) : -s*T.loU+T.c*(T.loV+T.side)≤4 := by
  have bound : 0≤4+s*T.loU-T.c*(T.loV+T.side) := by
    apply affine_endpoint_nonnegative T.side (s+T.c) _ T.side_pos
    intro epsilon positive small
    let u := T.loU+epsilon
    let v := T.loV+T.side-epsilon
    have point : T.Inside (T.c*u-T.s*v) (T.s*u+T.c*v) := by
      apply (inside_iff_rotated_box T _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      exact ⟨by linarith only [positive],by linarith only [small],
        by linarith only [small],by linarith only [positive]⟩
    have high := (box _ _ point).2.2.2
    dsimp [u,v] at high
    rw [sign] at high
    nlinarith only [high]
  linarith only [bound]

theorem faces (T : OpenSquare) (s : ℝ) (sign : T.s=-s)
    (normal : Normal T.c s) (side : 1<T.side)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20)) :
    (47/20)*(T.c+s)≤T.loV ∧
      ((87/50)*T.c-3*s≤T.loU ∨ 3*T.c+(87/50)*s≤T.loV) := by
  have b := normal_bounds normal
  have cp : 0<T.c := by linarith only [b.1]
  have m := (negative_bands T s _ _ sign).mp marker
  have r := (negative_bands T s _ _ sign).mp row
  have wing : (87/50)*T.c-3*s≤T.loU ∨ 3*T.c+(87/50)*s≤T.loV := by
    by_cases lower : (87/50)*T.c-3*s≤T.loU
    · exact Or.inl lower
    · right
      apply le_of_not_gt
      intro low
      apply missingWing
      apply (negative_bands T s _ _ sign).mpr
      exact ⟨by linarith only [lower],by nlinarith only [r.2.1,cp],
        by linarith only [low],by nlinarith only [r.2.2.2,normal.1]⟩
  have northeast : T.loU+T.side≤(47/20)*(T.c-s) ∨
      (47/20)*(T.c+s)≤T.loV := by
    by_cases upper : T.loU+T.side≤(47/20)*(T.c-s)
    · exact Or.inl upper
    · right
      apply le_of_not_gt
      intro low
      apply missingNE
      apply (negative_bands T s _ _ sign).mpr
      exact ⟨by nlinarith only [m.1,cp,normal.1],
        by linarith only [upper],by linarith only [low],
        by nlinarith only [r.2.2.2,cp,normal.1]⟩
  refine ⟨?_,wing⟩
  rcases northeast with upper | low
  · rcases wing with left | high
    · have short : (61/100)*T.c+(13/20)*s<1 := by
        have square : ((61/100)*T.c+(13/20)*s)^2≤3973/5000 := by
          nlinarith only [normal.2.2,sq_nonneg ((13/20)*T.c-(61/100)*s)]
        nlinarith only [square,sq_nonneg ((61/100)*T.c+(13/20)*s-1)]
      exfalso
      linarith only [upper,left,short,side]
    · nlinarith only [high,normal.2.1,cp]
  · exact low

private theorem coefficients (E T : OpenSquare) (s : ℝ)
    (en : Normal E.c E.s) (tn : Normal T.c s) :
    0≤E.c*T.c-E.s*s ∧ 0≤E.c*s+E.s*T.c ∧
      0<(E.c*T.c-E.s*s)+(E.c*s+E.s*T.c) := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have first := mul_nonneg (show 0≤E.c by linarith only [eb.1])
    (sub_nonneg.mpr tn.2.1)
  have last := mul_nonneg tn.1 (sub_nonneg.mpr en.2.1)
  have es := mul_nonneg (show 0≤E.c by linarith only [eb.1]) tn.1
  have fc := mul_nonneg en.1 (show 0≤T.c by linarith only [tb.1])
  have ec := mul_pos (show 0<E.c by linarith only [eb.1])
    (show 0<T.c by linarith only [tb.1])
  have rest := mul_nonneg en.1 (sub_nonneg.mpr tn.2.1)
  exact ⟨by nlinarith only [first,last],by linarith only [es,fc],
    by nlinarith only [ec,rest,es]⟩

theorem support_growth (T : OpenSquare) (s e f : ℝ) (sign : T.s=-s)
    (en : Normal e f) (tn : Normal T.c s) (side : 1<T.side)
    (box : InsideContainer T)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20)) :
    (7/2)*e+3*f+(3/5)*f<upper T e f+T.side := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have cp : 0<T.c := by linarith only [tb.1]
  let K := e*T.c-f*s
  let H := e*s+f*T.c
  have kp : 0≤K := by
    have first := mul_nonneg (show 0≤e by linarith only [eb.1])
      (sub_nonneg.mpr tn.2.1)
    have last := mul_nonneg tn.1 (sub_nonneg.mpr en.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg (by linarith only [eb.1]) tn.1)
      (mul_nonneg en.1 (by linarith only [tb.1]))
  have support : upper T e f=K*(T.loU+T.side)+H*(T.loV+T.side) :=
    upper_negative_pos T s e f sign kp hp
  have data := faces T s sign tn side marker row missingWing missingNE
  have wall := top_wall T s sign box
  rcases data.2 with lower | high
  · have first := mul_nonneg kp (sub_nonneg.mpr lower)
    have last := mul_nonneg hp (sub_nonneg.mpr data.1)
    have size := mul_pos (show 0<K+H+1 by linarith only [kp,hp]) (sub_pos.mpr side)
    have margin := forward_lower en tn
    have identity :
        K*((87/50)*T.c-3*s)+H*((47/20)*(T.c+s))+K+H+1-
          ((7/2)*e+3*f+(3/5)*f)=
        1+e*(T.c+s-44/25+(61/100)*s^2-(13/20)*T.c*s)+
          f*(T.c-s-5/4+(13/20)*s^2+(61/100)*T.c*s) := by
      dsimp [K,H]
      linear_combination ((87/50)*e+(47/20)*f)*tn.2.2
    nlinarith only [support,first,last,size,margin,identity]
  · have sine : 0<s := by
      by_contra no
      have zero : s=0 := by linarith only [no,tn.1]
      have cosine : T.c=1 := by nlinarith only [tn.2.2,zero,cp]
      nlinarith only [wall,high,side,zero,cosine]
    have first := mul_nonneg kp (show 0≤s*T.loU-T.c*(T.loV+T.side)+4 by
      linarith only [wall])
    have last := mul_nonneg (show 0≤e by linarith only [eb.1]) (sub_nonneg.mpr high)
    have sk := mul_nonneg tn.1 kp
    have size := mul_pos (show 0<e+s*K+s by linarith only [eb.1,sk,sine])
      (sub_pos.mpr side)
    have margin := forward_upper en tn
    have identity :
        e*(3*T.c+(87/50)*s+1)-4*K+s*K+s-
          s*((7/2)*e+3*f+(3/5)*f)=
        s+e*(1-T.c-(44/25)*s+T.c*s)+f*((2/5)*s-s^2) := by
      dsimp [K]; ring
    have scaled : s*(upper T e f+T.side-((7/2)*e+3*f+(3/5)*f))=
        K*(s*T.loU-T.c*(T.loV+T.side)+4)+
        e*(T.loV-(3*T.c+(87/50)*s))+
        (T.side-1)*(e+s*K+s)+
        (s+e*(1-T.c-(44/25)*s+T.c*s)+f*((2/5)*s-s^2)) := by
      rw [support]
      dsimp [K,H]
      linear_combination e*(T.loV+T.side)*tn.2.2
    have positive : 0<s*(upper T e f+T.side-((7/2)*e+3*f+(3/5)*f)) := by
      nlinarith only [scaled,first,last,size,margin]
    have result := pos_of_mul_pos_right positive sine.le
    linarith only [result]

private theorem reach_faces (E : OpenSquare) (en : Normal E.c E.s)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missing : ¬E.Inside (7/2) 3) :
    E.loU+E.side≤(7/2)*E.c+3*E.s ∨ 3*E.c-(7/2)*E.s≤E.loV := by
  have eb := normal_bounds en
  by_cases high : E.loU+E.side≤(7/2)*E.c+3*E.s
  · exact Or.inl high
  · right
    apply le_of_not_gt
    intro low
    apply missing
    refine ⟨?_,lt_of_not_ge high,low,?_⟩ <;>
      nlinarith only [outward.1,corner.2.2.2,eb.1,en.1]

theorem corner_axis_impossible (E T : OpenSquare) (s : ℝ) (sign : T.s=-s)
    (en : Normal E.c E.s) (tn : Normal T.c s)
    (same : E.side=T.side) (side : 1<E.side)
    (eBox : InsideContainer E) (tBox : InsideContainer T)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingReach : ¬E.Inside (7/2) 3)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (separator : upper T E.c E.s≤E.loU) : False := by
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have growth := support_growth T s E.c E.s sign en tn (by simpa only [←same] using side)
    tBox marker row missingWing missingNE
  rw [←same] at growth
  rcases reach_faces E en corner outward missingReach with high | low
  · nlinarith only [growth,separator,high,en.1]
  · have wall := UpperRightCornerLongitudinal.top_wall E eBox
    have first := mul_nonneg en.1 (sub_nonneg.mpr separator)
    have second := mul_nonneg ep.le (sub_nonneg.mpr low)
    have third := mul_nonneg en.1 (sub_nonneg.mpr growth.le)
    have size := mul_pos ep (sub_pos.mpr side)
    have product := mul_nonneg (sub_nonneg.mpr eb.2.1)
      (show 0≤(3/5)*E.c-2/5 by linarith only [eb.1])
    have margin : 1≤E.c+(3/5)*E.s^2 := by
      nlinarith only [product,en.2.2]
    nlinarith only [wall,first,second,third,size,margin,en.2.2]

theorem top_axis_impossible (E T : OpenSquare) (s : ℝ) (sign : T.s=-s)
    (en : Normal E.c E.s) (tn : Normal T.c s)
    (same : E.side=T.side) (side : 1<E.side)
    (eBox : InsideContainer E) (tBox : InsideContainer T)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingRight : ¬E.Inside 3 (12/5))
    (missingReach : ¬E.Inside (7/2) 3)
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (separator : T.loU+T.side≤lower E T.c (-s)) : False := by
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  let K := E.c*T.c-E.s*s
  let H := E.c*s+E.s*T.c
  let Q := (7/2)*E.c+3*E.s
  let F := (12/5)*E.c-3*E.s
  let P := 3*E.c-(7/2)*E.s
  let L := (87/50)*T.c-3*s
  let V := 3*T.c+(87/50)*s
  have coeff := coefficients E T s en tn
  have kp : 0≤K := coeff.1
  have hp : 0≤H := coeff.2.1
  have formula : lower E T.c (-s)=K*E.loU-H*(E.loV+E.side) := by
    rw [lower_in_bands]
    have first : T.c*E.c+(-s)*E.s=K := by dsimp [K]; ring
    have last : -T.c*E.s+(-s)*E.c=-H := by dsimp [H]; ring
    rw [first,last,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  rw [formula,←same] at separator
  have tf := faces T s sign tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  have tw := top_wall T s sign tBox
  rw [←same] at tw
  have ew := UpperRightCornerLongitudinal.top_wall E eBox
  have floor := UpperRightCornerReachAxes.lower_face E ep en.1 en.2.1 side
    corner outward missingRight missingReach
  rcases reach_faces E en corner outward missingReach with high | low
  · have first := mul_nonneg kp (show 0≤Q-E.loU-E.side by dsimp [Q]; linarith only [high])
    have last := mul_nonneg hp (show 0≤E.loV-F by dsimp [F]; linarith only [floor])
    have reduction : E.side*(1+K+H)+T.loU-K*Q+H*F≤0 := by
      nlinarith only [separator,first,last]
    rcases tf.2 with left | above
    · have size := mul_pos (show 0<1+K+H by linarith only [kp,hp]) (sub_pos.mpr side)
      have margin := reverse_lower_upper en tn
      have identity : 1+K+H+L-K*Q+H*F=
          1+T.c*(E.c+E.s-63/50-E.c^2/2-(3/5)*E.c*E.s)+
          s*(E.c-E.s-(3/5)*E.c^2+E.c*E.s/2) := by
        dsimp [K,H,L,Q,F]
        linear_combination (-3*T.c+3*s)*en.2.2
      dsimp [L] at identity
      nlinarith only [reduction,left,size,margin,identity]
    · have scaled := mul_nonpos_of_nonneg_of_nonpos tn.1 reduction
      have wall := mul_nonneg cp.le (show 0≤T.loV-V by dsimp [V]; linarith only [above])
      have sk := mul_nonneg tn.1 (show 0≤1+K+H by linarith only [kp,hp])
      have size := mul_pos (show 0<T.c+s*(1+K+H) by linarith only [cp,sk]) (sub_pos.mpr side)
      have margin := reverse_upper_upper en tn
      have identity : T.c+s*(1+K+H)+T.c*V-4-s*K*Q+s*H*F=
          T.c+s-1+s*(T.c*(E.c+E.s-63/50-E.c^2/2-(3/5)*E.c*E.s)+
            s*(E.c-E.s-(3/5)*E.c^2+E.c*E.s/2)) := by
        dsimp [K,H,V,Q,F]
        linear_combination 3*tn.2.2+s*(-3*T.c+3*s)*en.2.2
      nlinarith only [scaled,wall,tw,size,margin,identity]
  · have fp : 0<E.s := by
      by_contra no
      have zero : E.s=0 := by linarith only [no,en.1]
      have cosine : E.c=1 := by nlinarith only [en.2.2,zero,ep]
      nlinarith only [ew,low,zero,cosine,side]
    have sep := mul_nonneg en.1 (sub_nonneg.mpr separator)
    have wall := mul_nonneg kp (show 0≤4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side) by
      linarith only [ew])
    have lower := mul_nonneg cp.le (show 0≤E.loV-P by dsimp [P]; linarith only [low])
    have unit : K*E.c+H*E.s=T.c := by
      dsimp [K,H]; linear_combination T.c*en.2.2
    have reduction : E.side*(E.s+E.s*K+T.c)+E.s*T.loU+T.c*P-4*K≤0 := by
      have identity :
          E.s*(K*E.loU-H*(E.loV+E.side)-(T.loU+E.side))+
          K*(4-E.s*(E.loU+E.side)-E.c*(E.loV+E.side))+
          T.c*(E.loV-P)=
          -(E.side*(E.s+E.s*K+T.c)+E.s*T.loU+T.c*P-4*K) := by
        linear_combination -(E.loV+E.side)*unit
      nlinarith only [identity,sep,wall,lower]
    rcases tf.2 with left | above
    · have lw := mul_nonneg en.1 (show 0≤T.loU-L by dsimp [L]; linarith only [left])
      have fk := mul_nonneg en.1 kp
      have size := mul_pos (show 0<E.s+E.s*K+T.c by linarith only [fp,fk,cp]) (sub_pos.mpr side)
      have margin := reverse_lower_lower en tn
      have identity : E.s+E.s*K+T.c+E.s*L+T.c*P-4*K=
          T.c*(1-E.c)*(1-E.s)+E.s*(1-(19/25)*T.c)+s*E.s*(1-E.s) := by
        dsimp [K,L,P]; ring
      nlinarith only [reduction,lw,size,margin,identity]
    · have scaled := mul_nonpos_of_nonneg_of_nonpos tn.1 reduction
      have cw := mul_nonneg (mul_nonneg en.1 cp.le)
        (show 0≤T.loV-V by dsimp [V]; linarith only [above])
      have top := mul_nonneg en.1 (show 0≤4+s*T.loU-T.c*(T.loV+E.side) by
        linarith only [tw])
      have fk := mul_nonneg en.1 kp
      have sk := mul_nonneg tn.1 (show 0≤E.s+E.s*K+T.c by linarith only [fp,fk,cp])
      have fc := mul_pos fp cp
      have size := mul_pos (show 0<s*(E.s+E.s*K+T.c)+E.s*T.c by linarith only [sk,fc])
        (sub_pos.mpr side)
      have margin := reverse_upper_lower en tn
      have identity : s*(E.s+E.s*K+T.c)+E.s*T.c+
          E.s*T.c*V-4*E.s+s*T.c*P-4*s*K=
          T.c*E.s*(1-T.c)+s*T.c*(1-E.c)*(1-E.s)+
            s*E.s*(1-s*E.s-(19/25)*T.c) := by
        dsimp [K,V,P]
        linear_combination 4*E.s*tn.2.2
      nlinarith only [scaled,cw,top,size,margin,identity]

/-- The complete opposite-sign top/corner sector, including tangencies.
Only genuine strict anchors, full-square disjointness and containment
are used. The conclusion is a strict farther corner point. -/
theorem point (E T : OpenSquare) (s : ℝ) (sign : T.s=-s)
    (en : Normal E.c E.s) (tn : Normal T.c s)
    (same : E.side=T.side) (side : 1<E.side)
    (eBox : InsideContainer E) (tBox : InsideContainer T)
    (corner : E.Inside 3 3) (outward : E.Inside (16/5) 3)
    (missingRight : ¬E.Inside 3 (12/5))
    (marker : T.Inside 2 (1543/500)) (row : T.Inside (12/5) 3)
    (missingWing : ¬T.Inside (87/50) 3)
    (missingNE : ¬T.Inside (47/20) (47/20))
    (apart : ∀ x y, ¬(E.Inside x y ∧ T.Inside x y)) : E.Inside (7/2) 3 := by
  by_contra missing
  have eb := normal_bounds en
  have tb := normal_bounds tn
  have ep : 0<E.c := by linarith only [eb.1]
  have cp : 0<T.c := by linarith only [tb.1]
  have data := faces T s sign tn (by simpa only [←same] using side)
    marker row missingWing missingNE
  have floor := UpperRightCornerReachAxes.lower_face E ep en.1 en.2.1 side
    corner outward missingRight missing
  have longitudinal (c t : ℝ) (positive : 0<c) (canonical : t≤c)
      (unit : c^2+t^2=1)
      (sep : upper E c t≤lower T c t ∨ upper T c t≤lower E c t) :
      upper T c t≤lower E c t := by
    rcases sep with reverse | forward
    · have ePoint := strict_bounds E _ _ c t unit corner
      have tPoint := strict_bounds T _ _ c t unit marker
      exfalso
      nlinarith only [reverse,ePoint.2,tPoint.1,positive,canonical]
    · exact forward
  have axes := CongruentSAT.faceSeparation_of_disjoint E T same apart
  change pairRadius E T≤|E.c*(centerX T-centerX E)+E.s*(centerY T-centerY E)| ∨
    pairRadius E T≤|-E.s*(centerX T-centerX E)+E.c*(centerY T-centerY E)| ∨
    pairRadius T E≤|T.c*(centerX T-centerX E)+T.s*(centerY T-centerY E)| ∨
    pairRadius T E≤|-T.s*(centerX T-centerX E)+T.c*(centerY T-centerY E)| at axes
  have separateAxis (nx ny R : ℝ)
      (identity : supportRadius E nx ny+supportRadius T nx ny=R)
      (sep : R≤|nx*(centerX T-centerX E)+ny*(centerY T-centerY E)|) :=
    separated E T nx ny (by rwa [identity])
  rcases axes with eu | ev | tu | tv
  · have h := longitudinal E.c E.s ep en.2.1 E.unit_normal
      (separateAxis _ _ _ (parallel_radius E T) eu)
    rw [(ownU E).1] at h
    exact corner_axis_impossible E T s sign en tn same side eBox tBox
      corner outward missing marker row missingWing missingNE h
  · exact UpperRightCornerReachAxes.not_corner_transverse E T ep en.1 side
      corner marker row floor (separateAxis _ _ _ (transverse_radius E T) ev)
  · have identity : supportRadius E T.c T.s+supportRadius T T.c T.s=pairRadius T E := by
      rw [add_comm]; exact parallel_radius T E
    have h := longitudinal T.c T.s cp (by rw [sign]; linarith only [tn.1,cp])
      T.unit_normal (separateAxis _ _ _ identity tu)
    rw [(ownU T).2,sign] at h
    exact top_axis_impossible E T s sign en tn same side eBox tBox
      corner outward missingRight missing marker row missingWing missingNE h
  · have identity : supportRadius E (-T.s) T.c+supportRadius T (-T.s) T.c=pairRadius T E := by
      rw [add_comm]; exact transverse_radius T E
    have normal : s^2+T.c^2=1 := by nlinarith only [tn.2.2]
    have ePoint := strict_bounds E _ _ s T.c normal corner
    have tPoint := strict_bounds T _ _ s T.c normal row
    have sep := separateAxis _ _ _ identity tv
    rw [sign,neg_neg] at sep
    have lo : lower T s T.c=T.loV := by simpa only [sign,neg_neg] using (ownV T).1
    have hi : upper T s T.c=T.loV+T.side := by simpa only [sign,neg_neg] using (ownV T).2
    rcases sep with forward | reverse
    · rw [lo] at forward
      nlinarith only [forward,ePoint.2,tPoint.1,tn.1]
    · rw [hi,←same] at reverse
      have short : (13/20)*(T.c+s)<1 := by linarith only [tb.2.2.2.2.2]
      nlinarith only [reverse,ePoint.1,data.1,side,short]

end N12Compact.UpperRightNegativeTopReach
