import Compact.Completion.C981.LastPositiveScalars
import Compact.Completion.C981.NegativePair
import S12.Convex

/-! The complete small-positive central two-square ending for the last
C981 cycles. Whole diagonal absence is used as its actual supporting line,
not replaced by its endpoint absences. -/
namespace N12Compact.C981CompletionLastPositivePair

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C981CompletionSupportForms C977ChainBridge
set_option Elab.async false

theorem neighbor_faces_any (B : OpenSquare) (bn : Normal B.c B.s)
    (side : 1 < B.side)
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingLow : ¬ B.Inside 1 2) (missingInner : ¬ B.Inside (8/5) 2)
    (missingCorner : ¬ B.Inside 1 3) (missingTop : ¬ B.Inside (8/5) 3) :
    B.c+2*B.s ≤ B.loU ∧ 2*B.c-(8/5)*B.s ≤ B.loV ∧
      B.loU+B.side ≤ (8/5)*B.c+3*B.s ∧ B.loV+B.side ≤ 3*B.c-B.s := by
  have bounds := normal_bounds bn
  have bp : 0 < B.c := by linarith only [bounds.1]
  have kLowU : B.loU < B.c+3*B.s := by linarith only [high.1,bn.1]
  have kHighU : B.c+3*B.s < B.loU+B.side := by linarith only [marker.2.1,bn.2.1]
  have kLowV : B.loV < 3*B.c-B.s := by linarith only [high.2.2.1,bp]
  have kFace : B.loV+B.side ≤ 3*B.c-B.s := by
    apply le_of_not_gt
    intro upper
    apply missingCorner
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [kLowU,kHighU,kLowV,upper]
  have aHighU : B.c+2*B.s < B.loU+B.side := by linarith only [marker.2.1,bp,bn.1]
  have aLowV : B.loV < 2*B.c-B.s := by
    linarith only [kFace,side,bounds.2.1]
  have aHighV : 2*B.c-B.s < B.loV+B.side := by linarith only [high.2.2.2,bp]
  have aFace : B.c+2*B.s ≤ B.loU := by
    apply le_of_not_gt
    intro lowU
    apply missingLow
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lowU,aHighU,aLowV,aHighV]
  have dLowU : B.loU < (8/5)*B.c+2*B.s := by linarith only [low.1,bp,bn.2.1]
  have dHighU : (8/5)*B.c+2*B.s < B.loU+B.side := by linarith only [marker.2.1,bp,bn.1]
  have dHighV : 2*B.c-(8/5)*B.s < B.loV+B.side := by linarith only [marker.2.2.2,bp,bn.2.1]
  have dFace : 2*B.c-(8/5)*B.s ≤ B.loV := by
    apply le_of_not_gt
    intro lowV
    apply missingInner
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [dLowU,dHighU,lowV,dHighV]
  have pLowU : B.loU < (8/5)*B.c+3*B.s := by linarith only [low.1,bp,bn.1]
  have pLowV : B.loV < 3*B.c-(8/5)*B.s := by linarith only [marker.2.2.1,bp,bn.1]
  have pHighV : 3*B.c-(8/5)*B.s < B.loV+B.side := by linarith only [dFace,side,bounds.2.1]
  have pFace : B.loU+B.side ≤ (8/5)*B.c+3*B.s := by
    apply le_of_not_gt
    intro upper
    apply missingTop
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [pLowU,upper,pLowV,pHighV]
  exact ⟨aFace,dFace,pFace,kFace⟩

theorem neighbor_faces (B : OpenSquare) (bn : Normal B.c B.s)
    (side : 1 < B.side) (_angle : 1/2 ≤ B.s)
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingLow : ¬ B.Inside 1 2) (missingInner : ¬ B.Inside (8/5) 2)
    (missingCorner : ¬ B.Inside 1 3) (missingTop : ¬ B.Inside (8/5) 3) :
    B.c+2*B.s ≤ B.loU ∧ 2*B.c-(8/5)*B.s ≤ B.loV ∧
      B.loU+B.side ≤ (8/5)*B.c+3*B.s ∧ B.loV+B.side ≤ 3*B.c-B.s :=
  neighbor_faces_any B bn side marker low high missingLow missingInner missingCorner missingTop

private theorem diagonal_support (C : OpenSquare) (r : ℝ) (cs : C.s=r)
    (cn : Normal C.c r) (cp : 0 < C.c-r) (center : C.Inside 2 2)
    (capU : C.loU+C.side ≤ (113/50)*C.c+2*r)
    (capV : C.loV+C.side ≤ (113/50)*C.c-2*r)
    (avoid : ∀ z : ℝ, 0 ≤ z → z ≤ 13/50 → ¬ C.Inside (2+z) (113/50-z)) :
    (C.c+r)*(C.loU+C.side-2*(C.c+r))+
      (C.c-r)*(C.loV+C.side-2*(C.c-r)) ≤ 13/50 := by
  have noLine (x y : ℝ) (line : x+y=213/50) : ¬ C.Inside x y := by
    intro point
    have yEq : y=213/50-x := by linarith only [line]
    have lo : 2 < x := by
      have p := point.2.2.2
      rw [cs,yEq] at p
      have weight : 0 < (C.c+r)*(x-2) := by nlinarith only [p,capV]
      exact sub_pos.mp (pos_of_mul_pos_right weight (by linarith only [cn.1,cp]))
    have hi : x < 113/50 := by
      have p := point.2.1
      rw [cs,yEq] at p
      have weight : 0 < (C.c-r)*(113/50-x) := by nlinarith only [p,capU]
      exact sub_pos.mp (pos_of_mul_pos_right weight cp.le)
    have h := avoid (x-2) (by linarith only [lo]) (by linarith only [hi])
    apply h
    convert point using 1 <;> linarith only [line]
  have below (x y : ℝ) (point : C.Inside x y) : x+y ≤ 213/50 := by
    apply le_of_not_gt
    intro above
    let t := (13/50)/(x+y-4)
    have denominator : 0 < x+y-4 := by linarith only [above]
    have positive : 0 < t := div_pos (by norm_num) denominator
    have small : t < 1 := (div_lt_one denominator).mpr (by linarith only [above])
    have relation : t*(x+y-4)=13/50 := div_mul_cancel₀ _ denominator.ne'
    have point' := inside_segment C 2 2 x y t center point positive.le small.le
    exact noLine _ _ (by nlinarith only [relation]) point'
  have limit : 0 ≤ 213/50-
      ((C.c+r)*(C.loU+C.side)+(C.c-r)*(C.loV+C.side)) := by
    apply affine_endpoint_nonnegative C.side (2*C.c) _ C.side_pos
    intro t positive small
    let u := C.loU+C.side-t
    let v := C.loV+C.side-t
    have point : C.Inside (C.c*u-C.s*v) (C.s*u+C.c*v) := by
      apply (inside_iff_rotated_box C _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have bound := below _ _ point
    rw [cs] at bound
    dsimp [u,v] at bound
    nlinarith only [bound]
  nlinarith only [limit,cn.2.2]

theorem impossible (C B : OpenSquare) (r : ℝ) (cs : C.s=r)
    (cn : Normal C.c r) (bn : Normal B.c B.s)
    (side : 1 < C.side) (same : C.side=B.side)
    (small : r < 8/25) (angle : 1/2 ≤ B.s)
    (center : C.Inside 2 2) (west : C.Inside (69/50) 2) (bottom : C.Inside 2 (3/2))
    (southwest : C.Inside (33/20) (33/20))
    (missingNW : ¬ C.Inside (33/20) (47/20))
    (missingSE : ¬ C.Inside (47/20) (33/20))
    (diagonal : ∀ z : ℝ, 0 ≤ z → z ≤ 13/50 → ¬ C.Inside (2+z) (113/50-z))
    (marker : B.Inside (33/20) (47/20))
    (low : B.Inside 1 (113/50)) (high : B.Inside 1 (12/5))
    (missingLow : ¬ B.Inside 1 2) (missingInner : ¬ B.Inside (8/5) 2)
    (missingCorner : ¬ B.Inside 1 3) (missingTop : ¬ B.Inside (8/5) 3)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ B.Inside x y)) : False := by
  have cb := normal_bounds cn
  have bb := normal_bounds bn
  have ⟨cLarge,hSmall⟩ := C981CompletionLastPositiveScalars.small_bounds cn small
  have cp : 0 < C.c := by linarith only [cLarge]
  have bp : 0 < B.c := by linarith only [bb.1]
  have sp : 0 < B.s := by linarith only [angle]
  have sideB : 1 < B.side := by rwa [←same]
  have bBounds := C981CompletionLastPositiveScalars.neighbor_bounds bn angle
  have bands := neighbor_faces B bn sideB angle marker low high missingLow missingInner missingCorner missingTop
  have capV : C.loV+C.side ≤ -(33/20)*r+(47/20)*C.c := by
    apply le_of_not_gt
    intro upper
    apply missingNW
    refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
      linarith only [southwest.1,center.2.1,center.2.2.1,cp,cn.1,upper,cn.2.1,cs]
  have capU : C.loU+C.side ≤ (47/20)*C.c+(33/20)*r := by
    apply le_of_not_gt
    intro upper
    have short := (short_projections C (7/10) (7/10) (by norm_num)).2.1
    rw [cs] at short
    apply missingSE
    refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
      linarith only [center.1,center.2.2.2,cn.2.1,cp,cn.1,capV,short,side,upper,cs]
  let alpha := B.c*C.c+B.s*r
  let k := B.s*C.c-B.c*r
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos bp cp,mul_nonneg bn.1 cn.1]
  have kp : 0 < k := by
    have one := mul_nonneg cp.le (sub_nonneg.mpr angle)
    have two := mul_nonneg cn.1 (sub_nonneg.mpr bb.2.1)
    dsimp [k]
    nlinarith only [one,two,cLarge,small]
  have noCU (h : upper C C.c C.s ≤ lower B C.c C.s ∨
      upper B C.c C.s ≤ lower C C.c C.s) : False := by
    have own := strict_bounds C _ _ C.c C.s C.unit_normal center
    have other := strict_bounds B _ _ C.c C.s C.unit_normal marker
    have short := (short_projections C (7/10) (-(7/10)) (by norm_num)).2.1
    rw [cs] at own other short
    rcases h with forward | reverse
    · rw [cs] at forward
      nlinarith only [forward,own.2,other.1,cp,cn.2.1]
    · rw [(ownU C).1,cs] at reverse
      nlinarith only [reverse,other.2,capU,short,side]
  have noBU (h : upper C B.c B.s ≤ lower B B.c B.s ∨
      upper B B.c B.s ≤ lower C B.c B.s) : False := by
    rcases h with forward | reverse
    · have own := (strict_bounds C _ _ B.c B.s B.unit_normal center).2
      have other := (strict_bounds B _ _ B.c B.s B.unit_normal high).1
      nlinarith only [own,other,forward,bp,bn.2.1]
    · have support : lower C B.c B.s=alpha*C.loU+k*C.loV := by
        rw [lower_in_bands,cs]
        have u : B.c*C.c+B.s*r=alpha := rfl
        have v : -B.c*r+B.s*C.c=k := by dsimp [k]; ring
        rw [u,v,abs_of_pos ap,abs_of_pos kp]
        ring
      have ownV := bottom.2.2.1
      rw [cs] at ownV
      have first := mul_le_mul_of_nonneg_left
        (show C.loU ≤ (47/20)*C.c+(33/20)*r-1 by linarith only [capU,side]) ap.le
      have last := mul_lt_mul_of_pos_left
        (show C.loV < -2*r+(3/2)*C.c by linarith only [ownV]) kp
      let F := 7/10-C.c-(7/20)*r^2+(3/20)*C.c*r
      let G := -(17/20)-r+(3/20)*r^2+(7/20)*C.c*r
      have identity : alpha*((47/20)*C.c+(33/20)*r-1)+k*(-2*r+(3/2)*C.c)-
          ((33/20)*B.c+(47/20)*B.s)=B.c*F+B.s*G := by
        dsimp [alpha,k,F,G]
        linear_combination ((47/20)*B.c+(3/2)*B.s)*cn.2.2
      have dr := mul_nonneg cn.1 (sub_nonneg.mpr cb.2.1)
      have span := mul_nonneg cn.1 (show 0 ≤ 8/25-r by linarith only [small])
      have fn : F < 0 := by dsimp [F]; nlinarith only [cLarge,dr,small,sq_nonneg r]
      have gn : G < 0 := by dsimp [G]; nlinarith only [dr,span,small,cn.1]
      have f := mul_neg_of_pos_of_neg bp fn
      have g := mul_neg_of_pos_of_neg sp gn
      have other := (strict_bounds B _ _ B.c B.s B.unit_normal marker).2
      rw [support] at reverse
      have endpoint : alpha*((47/20)*C.c+(33/20)*r-1)+k*(-2*r+(3/2)*C.c) <
          (33/20)*B.c+(47/20)*B.s := by
        apply sub_neg.mp
        rw [identity]
        exact add_neg f g
      have otherBound : (33/20)*B.c+(47/20)*B.s < upper B B.c B.s := by
        convert other using 1 <;> ring
      exact (not_lt_of_ge reverse) (lt_trans (add_lt_add_of_le_of_lt first last)
        (lt_trans endpoint otherBound))
  have forward (x y : ℝ) (yp : 0 < y) (unit : x^2+y^2=1)
      (h : upper C x y ≤ lower B x y ∨ upper B x y ≤ lower C x y) :
      upper C x y ≤ lower B x y := by
    rcases h with h | h
    · exact h
    · have own := (strict_bounds C _ _ x y unit southwest).1
      have other := (strict_bounds B _ _ x y unit marker).2
      exfalso
      nlinarith only [h,own,other,yp]
  have axes := CongruentSAT.faceSeparation_of_disjoint C B same apart
  change pairRadius C B ≤ |C.c*(centerX B-centerX C)+C.s*(centerY B-centerY C)| ∨
    pairRadius C B ≤ |-C.s*(centerX B-centerX C)+C.c*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |B.c*(centerX B-centerX C)+B.s*(centerY B-centerY C)| ∨
    pairRadius B C ≤ |-B.s*(centerX B-centerX C)+B.c*(centerY B-centerY C)| at axes
  have sep (x y R : ℝ)
      (identity : supportRadius C x y+supportRadius B x y=R)
      (h : R ≤ |x*(centerX B-centerX C)+y*(centerY B-centerY C)|) :=
    separated C B x y (by rwa [identity])
  have modes : C.loV+C.side ≤ lower B (-r) C.c ∨ upper C (-B.s) B.c ≤ B.loV := by
    rcases axes with cu | cv | bu | bv
    · exact False.elim (noCU (sep _ _ _ (parallel_radius C B) cu))
    · have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
      have h := forward _ _ cp unit (sep _ _ _ (transverse_radius C B) cv)
      rw [(ownV C).2,cs] at h
      exact Or.inl h
    · have identity : supportRadius C B.c B.s+supportRadius B B.c B.s=pairRadius B C := by
        rw [add_comm]
        exact parallel_radius B C
      exact False.elim (noBU (sep _ _ _ identity bu))
    · have identity : supportRadius C (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B C := by
        rw [add_comm]
        exact transverse_radius B C
      have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
      have h := forward _ _ bp unit (sep _ _ _ identity bv)
      right
      simpa only [(ownV B).1] using h
  let u := C.loU+C.side-2*(C.c+r)
  let v := C.loV+C.side-2*(C.c-r)
  have uCap : u ≤ (7/20)*(C.c-r) := by dsimp [u]; linarith only [capU]
  have vLow : (31/50)*r < v := by
    have own := west.2.2.2
    rw [cs] at own
    dsimp [v]
    linarith only [own]
  rcases modes with cv | bv
  · have formula : lower B (-r) C.c=k*B.loU+alpha*B.loV := by
      rw [lower_in_bands]
      have first : (-r)*B.c+C.c*B.s=k := by dsimp [k]; ring
      have last : -(-r)*B.s+C.c*B.c=alpha := by dsimp [alpha]; ring
      rw [first,last,abs_of_pos kp,abs_of_pos ap]
      ring
    have first := mul_le_mul_of_nonneg_left
      (show B.loU ≤ (8/5)*B.c+3*B.s-1 by linarith only [bands.2.2.1,sideB]) kp.le
    have last := mul_le_mul_of_nonneg_left
      (show B.loV ≤ 3*B.c-B.s-1 by linarith only [bands.2.2.2,sideB]) ap.le
    let K := B.c+B.s-1-(3/5)*B.c*B.s
    let J := B.c-B.s-1/4+(3/5)*B.s^2
    have identity : k*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-2*(C.c-r)=
        -C.c*K+r*(J+13/20) := by
      dsimp [alpha,k,K,J]
      linear_combination (3*C.c-(8/5)*r)*bn.2.2
    rw [formula] at cv
    have vEndpoint : v ≤ -C.c*K+r*(J+13/20) := by
      calc
        v = C.loV+C.side-2*(C.c-r) := rfl
        _ ≤ k*B.loU+alpha*B.loV-2*(C.c-r) := sub_le_sub_right cv _
        _ ≤ k*((8/5)*B.c+3*B.s-1)+alpha*(3*B.c-B.s-1)-2*(C.c-r) :=
          sub_le_sub_right (add_le_add first last) _
        _ = _ := identity
    have kLower : 53/500 ≤ K := bBounds.2.2.1
    have jUpper : J+13/20 ≤ 917/1000 := by
      dsimp [J]
      linarith only [bBounds.2.2.2]
    have scalarEndpoint : -C.c*K+r*(J+13/20) ≤ -(53/500)*C.c+(917/1000)*r := by
      calc
        _ = -(C.c*K)+r*(J+13/20) := by ring
        _ ≤ -(C.c*(53/500))+r*(917/1000) :=
          add_le_add (neg_le_neg (mul_le_mul_of_nonneg_left kLower cp.le))
            (mul_le_mul_of_nonneg_left jUpper cn.1)
        _ = _ := by ring
    have scalarShort : -(53/500)*C.c+(917/1000)*r < (31/50)*r := by
      linarith only [cLarge,small]
    exact (not_lt_of_ge (le_trans vEndpoint
      (le_trans scalarEndpoint scalarShort.le))) vLow
  · have support : upper C (-B.s) B.c=-k*C.loU+alpha*(C.loV+C.side) := by
      rw [upper_in_bands,cs]
      have first : (-B.s)*C.c+B.c*r=-k := by dsimp [k]; ring
      have last : -(-B.s)*r+B.c*C.c=alpha := by dsimp [alpha]; ring
      rw [first,last,abs_of_nonpos (neg_nonpos.mpr kp.le),abs_of_pos ap]
      ring
    have excess : upper C (-B.s) B.c=2*(B.c-B.s)+C.side*k-k*u+alpha*v := by
      rw [support]
      dsimp [alpha,k,u,v]
      linear_combination 2*(B.c-B.s)*cn.2.2
    have dUlo : C.loU < (113/50)*C.c+2*r := by
      have own := center.1
      rw [cs] at own
      linarith only [own,cp]
    have dVlo : C.loV < -(113/50)*r+2*C.c := by
      have own := bottom.2.2.1
      rw [cs] at own
      linarith only [own,cp,cn.2.1]
    have dVhi : -(113/50)*r+2*C.c < C.loV+C.side := by
      have own := center.2.2.2
      rw [cs] at own
      linarith only [own,cn.1]
    have dFace : C.loU+C.side ≤ (113/50)*C.c+2*r := by
      apply le_of_not_gt
      intro high
      have missing := diagonal (13/50) (by norm_num) le_rfl
      apply missing
      refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
        linarith only [dUlo,high,dVlo,dVhi]
    have pUlo : C.loU < 2*C.c+(113/50)*r := by
      have own := center.1
      rw [cs] at own
      linarith only [own,cn.1]
    have pVlo : C.loV < -2*r+(113/50)*C.c := by
      have own := center.2.2.1
      rw [cs] at own
      linarith only [own,cp]
    have pModes : u ≤ (13/50)*r ∨ v ≤ (13/50)*C.c := by
      by_cases first : u ≤ (13/50)*r
      · exact Or.inl first
      · right
        apply le_of_not_gt
        intro high
        have missing := diagonal 0 le_rfl (by norm_num)
        apply missing
        refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;> dsimp [u,v] at first high <;>
          linarith only [pUlo,first,pVlo,high]
    have strict : 1+k < C.side*(1+k) := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right side
        (show 0 < 1+k by linarith only [kp])
    rw [←same] at bands
    rcases pModes with pU | pV
    · have cut : 1 < B.c*(1+r-(13/50)*r^2-(31/50)*C.c*r)+
          B.s*(1-C.c+(13/50)*C.c*r-(31/50)*r^2) := by
        have lowerBound : 2*(B.c-B.s)+C.side*k-k*((13/50)*r)+alpha*((31/50)*r) ≤
            upper C (-B.s) B.c := by
          calc
            _ ≤ 2*(B.c-B.s)+C.side*k-k*u+alpha*((31/50)*r) :=
              add_le_add_right (sub_le_sub_left (mul_le_mul_of_nonneg_left pU kp.le) _) _
            _ ≤ 2*(B.c-B.s)+C.side*k-k*u+alpha*v :=
              add_le_add_left (mul_le_mul_of_nonneg_left vLow.le ap.le) _
            _ = upper C (-B.s) B.c := excess.symm
        have combined := le_trans (add_le_add_right (le_trans lowerBound bv) C.side) bands.2.2.2
        have endpoint : C.side*(1+k) ≤ B.c+B.s+k*((13/50)*r)-alpha*((31/50)*r) := by
          calc
            _ = (2*(B.c-B.s)+C.side*k-k*((13/50)*r)+alpha*((31/50)*r)+C.side)-
                (2*(B.c-B.s)-k*((13/50)*r)+alpha*((31/50)*r)) := by ring
            _ ≤ (3*B.c-B.s)-(2*(B.c-B.s)-k*((13/50)*r)+alpha*((31/50)*r)) :=
              sub_le_sub_right combined _
            _ = _ := by ring
        have identity : B.c*(1+r-(13/50)*r^2-(31/50)*C.c*r)+
            B.s*(1-C.c+(13/50)*C.c*r-(31/50)*r^2)=
            (B.c+B.s+k*((13/50)*r)-alpha*((31/50)*r))-k := by
          dsimp [alpha,k]
          ring
        rw [identity]
        exact (lt_sub_iff_add_lt).mpr (lt_of_lt_of_le strict endpoint)
      exact C981CompletionLastPositiveScalars.first_impossible C.c r B.c B.s cn bn small angle cut
    · have vCap : C.loV+C.side ≤ (113/50)*C.c-2*r := by dsimp [v] at pV; linarith only [pV]
      have support := diagonal_support C r cs cn
        (by linarith only [cLarge,small]) center dFace vCap diagonal
      change (C.c+r)*u+(C.c-r)*v ≤ 13/50 at support
      have hPositive : 0 < C.c+r := by linarith only [cp,cn.1]
      have unitIdentity : k*(C.c-r)+alpha*(C.c+r)=B.c+B.s := by
        dsimp [alpha,k]
        linear_combination (B.c+B.s)*cn.2.2
      have scaled : C.c+r < (C.c+r)*(B.c*(1+r)+B.s*(13/50+1-C.c))-
          (22/25)*(B.c+B.s)*r := by
        have combined := le_trans (add_le_add_right bv C.side) bands.2.2.2
        rw [excess] at combined
        have endpoint : C.side*(1+k) ≤ B.c+B.s+k*u-alpha*v := by
          calc
            _ = (2*(B.c-B.s)+C.side*k-k*u+alpha*v+C.side)-
                (2*(B.c-B.s)-k*u+alpha*v) := by ring
            _ ≤ (3*B.c-B.s)-(2*(B.c-B.s)-k*u+alpha*v) :=
              sub_le_sub_right combined _
            _ = _ := by ring
        have scaledEndpoint := mul_le_mul_of_nonneg_left endpoint hPositive.le
        have supportWeighted := mul_le_mul_of_nonneg_left support kp.le
        have projectionBound : (C.c+r)*(B.c+B.s+k*u-alpha*v) ≤
            (C.c+r)*(B.c+B.s)+(13/50)*k-(B.c+B.s)*v := by
          calc
            _ = (C.c+r)*(B.c+B.s)+k*((C.c+r)*u+(C.c-r)*v)-
                (k*(C.c-r)+alpha*(C.c+r))*v := by ring
            _ ≤ (C.c+r)*(B.c+B.s)+k*(13/50)-
                (k*(C.c-r)+alpha*(C.c+r))*v :=
              sub_le_sub_right (add_le_add_left supportWeighted _) _
            _ = _ := by rw [unitIdentity]; ring
        have vBound : (C.c+r)*(B.c+B.s)+(13/50)*k-(B.c+B.s)*v ≤
            (C.c+r)*(B.c+B.s)+(13/50)*k-(31/50)*(B.c+B.s)*r := by
          calc
            _ ≤ (C.c+r)*(B.c+B.s)+(13/50)*k-(B.c+B.s)*((31/50)*r) :=
              sub_le_sub_left (mul_le_mul_of_nonneg_left vLow.le (add_nonneg bp.le bn.1)) _
            _ = _ := by ring
        have scaledStrict := mul_lt_mul_of_pos_left strict hPositive
        have last := lt_of_lt_of_le scaledStrict
          (le_trans scaledEndpoint (le_trans projectionBound vBound))
        have scaledIdentity : (C.c+r)*(B.c*(1+r)+B.s*(13/50+1-C.c))-
            (22/25)*(B.c+B.s)*r=
            (C.c+r)*(B.c+B.s)+(13/50)*k-(31/50)*(B.c+B.s)*r-(C.c+r)*k := by
          dsimp [k]
          ring
        rw [scaledIdentity]
        apply (lt_sub_iff_add_lt).mpr
        convert last using 1 <;> ring
      have identity : (C.c+r)*(B.c*(1+r-(22/25)*r/(C.c+r))+
          B.s*(13/50+1-C.c-(22/25)*r/(C.c+r))-1)=
          (C.c+r)*(B.c*(1+r)+B.s*(13/50+1-C.c))-
            (22/25)*(B.c+B.s)*r-(C.c+r) := by
        field_simp [hPositive.ne'] <;> ring
      have cut : 1 < B.c*(1+r-(22/25)*r/(C.c+r))+
          B.s*(13/50+(1-C.c)-(22/25)*r/(C.c+r)) := by
        have product : 0 < (C.c+r)*(B.c*(1+r-(22/25)*r/(C.c+r))+
            B.s*(13/50+1-C.c-(22/25)*r/(C.c+r))-1) := by
          rw [identity]
          linarith only [scaled]
        have gap := pos_of_mul_pos_right product hPositive.le
        linarith only [gap]
      exact C981CompletionLastPositiveScalars.second_impossible C.c r B.c B.s cn bn small angle cut

#print axioms impossible
end N12Compact.C981CompletionLastPositivePair
