import Compact.Completion.C981.NegativePoint
import S12.ShortCluster.Projections

/-! Complete retained negative/negative two-square ending. Every face
normal and relative-angle order is retained. The three foreign absences
must come from their actual owners in the original packing. -/
namespace N12Compact.C981CompletionNegativePair

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C981CompletionSupportForms
open C977ChainBridge
set_option Elab.async false

theorem lower_pp (q : OpenSquare) (x y : ℝ)
    (hu : 0 ≤ x*q.c+y*q.s) (hv : 0 ≤ -x*q.s+y*q.c) :
    lower q x y=(x*q.c+y*q.s)*q.loU+(-x*q.s+y*q.c)*q.loV := by
  rw [lower_in_bands,abs_of_nonneg hu,abs_of_nonneg hv]
  ring

theorem central_cap (C : OpenSquare) (r : ℝ) (cs : C.s=-r) (cn : Normal C.c r)
    (center : C.Inside 2 2) (bottom : C.Inside 2 (3/2))
    (missing : ¬ C.Inside (47/20) (33/20)) :
    C.loU+C.side ≤ (47/20)*C.c-(33/20)*r := by
  have cb := normal_bounds cn
  have cp : 0 < C.c := by linarith only [cb.1]
  apply le_of_not_gt
  intro upper
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;> rw [cs]
  · have own := center.1
    rw [cs] at own
    linarith only [own,cp,cn.1]
  · linarith only [upper]
  · have own := bottom.2.2.1
    rw [cs,neg_neg] at own
    linarith only [own,cp,cn.1]
  · have own := center.2.2.2
    rw [cs,neg_neg] at own
    linarith only [own,cn.2.1]

private theorem alternatives (C B : OpenSquare) (r t : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1 < C.side) (same : C.side=B.side)
    (cap : C.loU+C.side ≤ (47/20)*C.c-(33/20)*r)
    (center : C.Inside 2 2) (southwest : C.Inside (33/20) (33/20))
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) :
    B.loU+B.side ≤ lower C B.c (-t) ∨
      C.loV+C.side ≤ lower B r C.c ∨ upper C t B.c ≤ B.loV := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  have noCU (h : upper C C.c C.s ≤ lower B C.c C.s ∨
      upper B C.c C.s ≤ lower C C.c C.s) : False := by
    have own := strict_bounds C _ _ C.c C.s C.unit_normal center
    have other := strict_bounds B _ _ C.c C.s C.unit_normal marker
    have short := (short_projections C (7/10) (-(7/10)) (by norm_num)).2.1
    rw [cs] at own other short
    rcases h with forward | reverse
    · rw [cs] at forward
      nlinarith only [forward,own.2,other.1,cp,cn.1]
    · rw [(ownU C).1] at reverse
      rw [cs] at reverse
      nlinarith only [reverse,other.2,cap,short,side]
  have forward (x y : ℝ) (yp : 0 < y) (unit : x^2+y^2=1)
      (h : upper C x y ≤ lower B x y ∨ upper B x y ≤ lower C x y) :
      upper C x y ≤ lower B x y := by
    rcases h with h | h
    · exact h
    · have own := (strict_bounds C _ _ x y unit southwest).1
      have other := (strict_bounds B _ _ x y unit marker).2
      exfalso; nlinarith only [h,own,other,yp]
  have axes := CongruentSAT.faceSeparation_of_disjoint C B same apart
  change pairRadius C B ≤ |C.c*(centerX B-centerX C)+C.s*(centerY B-centerY C)| ∨
    pairRadius C B ≤ |-C.s*(centerX B-centerX C)+C.c*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |B.c*(centerX B-centerX C)+B.s*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |-B.s*(centerX B-centerX C)+B.c*(centerY B-centerY C)| at axes
  have sep (x y R : ℝ)
      (identity : supportRadius C x y+supportRadius B x y=R)
      (h : R ≤ |x*(centerX B-centerX C)+y*(centerY B-centerY C)|) :=
    separated C B x y (by rwa [identity])
  rcases axes with cu | cv | bu | bv
  · exact False.elim (noCU (sep _ _ _ (parallel_radius C B) cu))
  · have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
    have h := forward _ _ cp unit (sep _ _ _ (transverse_radius C B) cv)
    right; left
    rw [(ownV C).2] at h
    simpa only [cs,neg_neg] using h
  · have identity : supportRadius C B.c B.s+supportRadius B B.c B.s=pairRadius B C := by
      rw [add_comm]; exact parallel_radius B C
    rcases sep _ _ _ identity bu with first | last
    · have own := (strict_bounds C _ _ B.c B.s B.unit_normal center).2
      have other := (strict_bounds B _ _ B.c B.s B.unit_normal high).1
      rw [bs] at own other first
      exfalso; nlinarith only [own,other,first,bp,bn.1]
    · left
      rw [(ownU B).2] at last
      simpa only [bs] using last
  · have identity : supportRadius C (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B C := by
      rw [add_comm]; exact transverse_radius B C
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have h := forward _ _ bp unit (sep _ _ _ identity bv)
    right; right
    rw [(ownV B).1] at h
    simpa only [bs,neg_neg] using h

private theorem shallow_long_impossible (C B : OpenSquare) (r t : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1 < C.side) (cap : C.loU+C.side ≤ (47/20)*C.c-(33/20)*r)
    (bottom : C.Inside 2 (3/2)) (marker : B.Inside (33/20) (47/20))
    (angle : 0 ≤ B.c*r-t*C.c)
    (long : B.loU+B.side ≤ lower C B.c (-t)) : False := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  have rBound : r ≤ 5/7 := by nlinarith only [cn.2.2,cb.1,cn.1,sq_nonneg (C.c-7/10),sq_nonneg (r-5/7)]
  let alpha := B.c*C.c+t*r
  let h := B.c*r-t*C.c
  let F := 7/10-C.c-(7/20)*r^2-(3/20)*C.c*r
  let G := 17/20-r-(3/20)*r^2+(7/20)*C.c*r
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos bp cp,mul_nonneg bn.1 cn.1]
  have hp : 0 ≤ h := angle
  have gp : 0 ≤ G := by
    have product := mul_nonneg cn.1 (sub_nonneg.mpr cn.2.1)
    dsimp [G]
    nlinarith only [product,rBound,sq_nonneg r]
  have support : lower C B.c (-t)=alpha*C.loU+h*C.loV := by
    have raw := lower_negative_pos C r B.c (-t) cs
      (show 0 ≤ B.c*C.c-(-t)*r by dsimp [alpha] at ap; nlinarith only [ap])
      (show 0 ≤ B.c*r+(-t)*C.c by dsimp [h] at hp; nlinarith only [hp])
    dsimp [alpha,h]
    nlinarith only [raw]
  have ownV := bottom.2.2.1
  rw [cs,neg_neg] at ownV
  have first := mul_nonneg ap.le
    (show 0 ≤ (47/20)*C.c-(33/20)*r-1-C.loU by linarith only [cap,side])
  have last := mul_nonneg hp (show 0 ≤ 2*r+(3/2)*C.c-C.loV by linarith only [ownV])
  have identity : alpha*((47/20)*C.c-(33/20)*r-1)+h*(2*r+(3/2)*C.c)-
      ((33/20)*B.c-(47/20)*t)=B.c*F+t*G := by
    dsimp [alpha,h,F,G]
    linear_combination ((47/20)*B.c-(3/2)*t)*cn.2.2
  have cancellation : C.c*F+r*G=(7/10)*(C.c+r)-1 := by
    dsimp [F,G]
    linear_combination -(1+(3/20)*r)*cn.2.2
  have weight : C.c*(B.c*F+t*G)=B.c*(C.c*F+r*G)-h*G := by dsimp [h]; ring
  have one := mul_nonpos_of_nonneg_of_nonpos bp.le
    (show (7/10)*(C.c+r)-1 ≤ 0 by linarith only [cb.2.2.2.2.2])
  have two := mul_nonneg hp gp
  have polynomial : B.c*F+t*G ≤ 0 := by
    have weighted : C.c*(B.c*F+t*G) ≤ 0 := by
      rw [weight,cancellation]
      exact sub_nonpos.mpr (one.trans two)
    exact nonpos_of_mul_nonpos_right weighted cp
  have mark := marker.2.1
  rw [bs] at mark
  rw [support] at long
  have uBound : C.loU≤(47/20)*C.c-(33/20)*r-1 := by
    linarith only [cap,side]
  have vBound : C.loV≤2*r+(3/2)*C.c := by linarith only [ownV]
  have upperBound := add_le_add
    (mul_le_mul_of_nonneg_left uBound ap.le)
    (mul_le_mul_of_nonneg_left vBound hp)
  have lastBound : alpha*((47/20)*C.c-(33/20)*r-1)+h*(2*r+(3/2)*C.c)≤
      (33/20)*B.c-(47/20)*t := by
    apply sub_nonpos.mp
    rw [identity]
    exact polynomial
  have markerLow : (33/20)*B.c-(47/20)*t<B.loU+B.side := by
    linarith only [mark]
  exact (not_lt_of_ge (long.trans (upperBound.trans lastBound))) markerLow

private theorem deep_long_impossible (C B : OpenSquare) (r t : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1 < C.side) (same : C.side=B.side)
    (cap : C.loU+C.side ≤ (47/20)*C.c-(33/20)*r)
    (center : C.Inside 2 2) (marker : B.Inside (33/20) (47/20))
    (high : B.Inside 1 (12/5))
    (missingCorner : ¬ B.Inside 1 3) (missingWall : ¬ B.Inside (457/500) 2)
    (angle : B.c*r-t*C.c < 0)
    (long : B.loU+B.side ≤ lower C B.c (-t)) : False := by
  classical
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have cp : 0 < C.c := by linarith only [cb.1]
  have bp : 0 < B.c := by linarith only [bb.1]
  let alpha := B.c*C.c+t*r
  let k := t*C.c-B.c*r
  let u := C.loU+C.side-2*(C.c-r)
  let v := C.loV+C.side-2*(C.c+r)
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos bp cp,mul_nonneg bn.1 cn.1]
  have kp : 0 < k := by dsimp [k]; linarith only [angle]
  have vp : 0 < v := by
    have own := center.2.2.2
    rw [cs,neg_neg] at own
    dsimp [v]; linarith only [own]
  have uCap : u ≤ (7/20)*(C.c+r) := by dsimp [u]; linarith only [cap]
  have support : lower C B.c (-t)=alpha*C.loU-k*(C.loV+C.side) := by
    rw [lower_in_bands,cs]
    have u : B.c*C.c+(-t)*(-r)=alpha := by dsimp [alpha]; ring
    have v : -B.c*(-r)+(-t)*C.c=-k := by dsimp [k]; ring
    rw [u,v,abs_of_nonneg ap.le,abs_of_nonpos (neg_nonpos.mpr kp.le)]
    ring
  have supportExcess : lower C B.c (-t)=
      2*(B.c-t)+alpha*u-alpha*C.side-k*v := by
    rw [support]
    dsimp [alpha,k,u,v]
    linear_combination 2*(B.c-t)*cn.2.2
  have mark := marker.2.1
  rw [bs] at mark
  have size := mul_pos ap (sub_pos.mpr side)
  have cut : 0 < (7/20)*(B.c+t)-alpha*(1-u)-k*v := by
    have markerLow : (33/20)*B.c-(47/20)*t<B.loU+B.side := by
      linarith only [mark]
    have gap : 0<lower C B.c (-t)-((33/20)*B.c-(47/20)*t) :=
      sub_pos.mpr (markerLow.trans_le long)
    have identity : (7/20)*(B.c+t)-alpha*(1-u)-k*v=
        (lower C B.c (-t)-((33/20)*B.c-(47/20)*t))+alpha*(C.side-1) := by
      rw [supportExcess]
      ring
    rw [identity]
    exact add_pos gap size
  have slope : B.c < 4*t := by
    apply lt_of_not_ge
    intro no
    have rSmall : r < 1/4 := by
      have first := mul_nonneg cn.1 (show 0 ≤ B.c-4*t by linarith only [no])
      have kpRaw : B.c*r<t*C.c := sub_pos.mp kp
      have positive : 0<t*C.c := lt_of_le_of_lt (mul_nonneg bp.le cn.1) kpRaw
      have tp : 0<t := pos_of_mul_pos_left positive cp.le
      have product : 0 < t*(C.c-4*r) := by
        have identity : t*(C.c-4*r)=k+r*(B.c-4*t) := by dsimp [k]; ring
        rw [identity]
        exact add_pos_of_pos_of_nonneg kp first
      have bound : 4*r < C.c := by
        have positive := pos_of_mul_pos_right product tp.le
        linarith only [positive]
      linarith only [bound,cb.2.1]
    have cLarge : 24/25 ≤ C.c := by
      have product := mul_nonneg cn.1 (show 0≤1/4-r by linarith only [rSmall])
      have rSquare : r^2<1/16 := by nlinarith only [product,rSmall]
      apply le_of_not_gt
      intro small
      have square := mul_nonneg
        (show 0≤24/25-C.c by linarith only [small])
        (show 0≤24/25+C.c by linarith only [cp])
      nlinarith only [cn.2.2,rSquare,square]
    have uSmall : u ≤ 7/16 := by linarith only [uCap,cb.2.1,rSmall]
    have alphaLarge : (24/25)*B.c ≤ alpha := by
      have first := mul_nonneg bp.le (sub_nonneg.mpr cLarge)
      dsimp [alpha]
      nlinarith only [first,mul_nonneg bn.1 cn.1]
    have first := mul_nonneg ap.le (show 0 ≤ 1-u-9/16 by linarith only [uSmall])
    have last := mul_nonneg (show 0 ≤ alpha-(24/25)*B.c by linarith only [alphaLarge])
      (by norm_num : (0:ℝ) ≤ 9/16)
    have remaining := mul_nonneg kp.le vp.le
    have lower : (27/50)*B.c≤alpha*(1-u) := by
      calc
        (27/50)*B.c=((24/25)*B.c)*(9/16) := by ring
        _≤alpha*(9/16) := mul_le_mul_of_nonneg_right alphaLarge (by norm_num)
        _≤alpha*(1-u) := mul_le_mul_of_nonneg_left
          (show (9/16:ℝ)≤1-u by linarith only [uSmall]) ap.le
    have sumUpper : (7/20)*(B.c+t)≤(7/16)*B.c := by linarith only [no]
    have nonpositive : (7/20)*(B.c+t)-alpha*(1-u)-k*v≤0 := by
      calc
        (7/20)*(B.c+t)-alpha*(1-u)-k*v≤(7/20)*(B.c+t)-alpha*(1-u) :=
          sub_le_self _ remaining
        _≤(7/16)*B.c-(27/50)*B.c := sub_le_sub sumUpper lower
        _≤0 := by linarith only [bp]
    exact (not_lt_of_ge nonpositive) cut
  have wUlo : B.loU < (457/500)*B.c-2*t := by
    have own := high.1
    rw [bs] at own
    linarith only [own,slope,bp]
  have wUhi : (457/500)*B.c-2*t < B.loU+B.side := by
    linarith only [mark,bp,bn.2.1]
  have wVhi : (457/500)*t+2*B.c < B.loV+B.side := by
    have own := marker.2.2.2
    rw [bs,neg_neg] at own
    linarith only [own,bp,bn.1]
  have wFace : (457/500)*t+2*B.c ≤ B.loV := by
    apply le_of_not_gt
    intro low
    apply missingWall
    refine ⟨?_,?_,?_,?_⟩ <;> rw [bs] <;>
      linarith only [wUlo,wUhi,low,wVhi]
  have sine : 7/40 < t := by linarith only [slope,bb.1]
  have short : B.c+(43/500)*t < 1 := by
    have defect : B.c+t^2/2 ≤ 1 := by nlinarith only [bn.2.2,sq_nonneg (1-B.c)]
    have product := mul_pos (show 0 < t by linarith only [sine])
      (show 0 < t/2-43/500 by linarith only [sine])
    nlinarith only [defect,product]
  have kUhi : B.c-3*t < B.loU+B.side := by
    have own := high.2.1
    rw [bs] at own
    linarith only [own,bn.1]
  have kVlo : B.loV < t+3*B.c := by
    have own := high.2.2.1
    rw [bs,neg_neg] at own
    linarith only [own,bp]
  have kVhi : t+3*B.c < B.loV+B.side := by
    rw [same] at side
    linarith only [wFace,short,side]
  have kFace : B.c-3*t ≤ B.loU := by
    apply le_of_not_gt
    intro low
    apply missingCorner
    refine ⟨?_,?_,?_,?_⟩ <;> rw [bs] <;> linarith only [low,kUhi,kVlo,kVhi]
  have necessary : 1 < B.c+t-alpha*(1-(7/20)*(C.c+r)) := by
    have first := mul_nonneg ap.le (sub_nonneg.mpr uCap)
    have last := mul_nonneg kp.le vp.le
    have size := mul_pos (show 0 < 1+alpha by linarith only [ap]) (sub_pos.mpr side)
    have longSame : B.loU+C.side ≤ lower C B.c (-t) := by simpa only [same] using long
    have gap : 0≤lower C B.c (-t)-(B.c-3*t+C.side) :=
      sub_nonneg.mpr ((add_le_add_right kFace C.side).trans longSame)
    have identity : B.c+t-alpha*(1-(7/20)*(C.c+r))-1=
        (lower C B.c (-t)-(B.c-3*t+C.side))+(1+alpha)*(C.side-1)+
          alpha*((7/20)*(C.c+r)-u)+k*v := by
      rw [supportExcess]
      ring
    apply sub_pos.mp
    rw [identity]
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos gap size) first) last
  let H := C.c+r
  let q := 1-(7/20)*H
  have qp : 0 ≤ q := by dsimp [q,H]; linarith only [cb.2.2.2.2.2]
  have hq : 13/20 ≤ H*q := by
    have product := mul_nonneg
      (show 0 ≤ H-1 by dsimp [H]; linarith only [cb.2.2.2.2.1])
      (show 0 ≤ 13/20-(7/20)*H by dsimp [H]; linarith only [cb.2.2.2.2.2])
    dsimp [q] at ⊢
    nlinarith only [product]
  have alphaLower : (B.c+t)*H ≤ 2*alpha := by
    have product := mul_nonneg (sub_nonneg.mpr bn.2.1) (sub_nonneg.mpr cn.2.1)
    dsimp [H,alpha]
    nlinarith only [product]
  have one := mul_nonneg qp (sub_nonneg.mpr alphaLower)
  have two := mul_nonneg (show 0 ≤ B.c+t by linarith only [bp,bn.1])
    (sub_nonneg.mpr hq)
  have three : (27/40)*(B.c+t) ≤ 27/28 := by linarith only [bb.2.2.2.2.2]
  change 1 < B.c+t-alpha*q at necessary
  have combined : 0≤2*(alpha*q)-(13/20)*(B.c+t) := by
    convert add_nonneg one two using 1 <;> ring
  have lower : (13/40)*(B.c+t)≤alpha*q := by linarith only [combined]
  have upper : B.c+t-alpha*q≤(27/40)*(B.c+t) := by
    calc
      B.c+t-alpha*q≤B.c+t-(13/40)*(B.c+t) := sub_le_sub_left lower _
      _=(27/40)*(B.c+t) := by ring
  have impossible : (1:ℝ)<27/28 := necessary.trans_le (upper.trans three)
  norm_num at impossible

/-- The entire negative/negative canonical sector, with no outer square
or container premise after the genuine center/crosspoint entrance. -/
theorem impossible (C B : OpenSquare) (r t : ℝ)
    (cs : C.s=-r) (cn : Normal C.c r) (bs : B.s=-t) (bn : Normal B.c t)
    (side : 1 < C.side) (same : C.side=B.side)
    (center : C.Inside 2 2) (bottom : C.Inside 2 (3/2))
    (southwest : C.Inside (33/20) (33/20))
    (missing : ¬ C.Inside (47/20) (33/20))
    (marker : B.Inside (33/20) (47/20)) (high : B.Inside 1 (12/5))
    (missingTop : ¬ B.Inside (8/5) 3) (missingCorner : ¬ B.Inside 1 3)
    (missingWall : ¬ B.Inside (457/500) 2)
    (apart : ∀ x y, ¬(C.Inside x y ∧ B.Inside x y)) : False := by
  have cap := central_cap C r cs cn center bottom missing
  have modes := alternatives C B r t cs cn bs bn side same cap center southwest marker high apart
  rcases modes with long | cv | bv
  · by_cases angle : 0 ≤ B.c*r-t*C.c
    · exact shallow_long_impossible C B r t cs cn bs bn side cap bottom marker angle long
    · exact deep_long_impossible C B r t cs cn bs bn side same cap center marker high
        missingCorner missingWall (lt_of_not_ge angle) long
  · exact missingTop (C981CompletionNegativePoint.point C B r t cs cn bs bn (by rwa [←same])
      center marker high (Or.inl cv))
  · exact missingTop (C981CompletionNegativePoint.point C B r t cs cn bs bn (by rwa [←same])
      center marker high (Or.inr (by simpa only [bs,neg_neg] using bv)))

#print axioms impossible
end N12Compact.C981CompletionNegativePair
