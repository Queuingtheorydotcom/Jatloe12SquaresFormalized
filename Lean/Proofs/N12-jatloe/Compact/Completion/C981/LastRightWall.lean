import Compact.Completion.C981.LastRightFaces

/-! The actual arbitrary-angle wall owner forces the neighboring central
square past sine1/2. This is the full support argument, including contact. -/
namespace N12Compact.C981CompletionLastRightWall

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C981CompletionLastRightScalars C981CompletionLastRightFaces
open C981CompletionSupportForms
set_option Elab.async false

private theorem positive (B R : OpenSquare) (bn : Normal B.c B.s)
    (rc : 0 < R.c) (rs : 0 ≤ R.s) (side : 1 < B.side) (same : B.side=R.side)
    (minor : Minor B.c B.s)
    (bands : -B.c ≤ B.loU ∧ (2/5)*B.s ≤ B.loV ∧
      B.loU+B.side ≤ B.s-(2/5)*B.c ∧ B.loV+B.side ≤ B.c+B.s)
    (marker : B.Inside (-(7/20)) (7/20)) (high : B.Inside (-1) (2/5))
    (wall : ∀ x y, R.Inside x y → y ≤ 2)
    (rA : R.Inside (-(2/5)) 1) (rD : R.Inside (13/50) 1)
    (rT : ¬ R.Inside (2/5) 1)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)) : False := by
  let alpha := B.c*R.c+B.s*R.s
  let beta := B.c*R.s-B.s*R.c
  have bp : 0 < B.c := by linarith only [minor.bLow]
  have tp : 0 < B.s := by linarith only [minor.tLow]
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos bp rc,mul_nonneg bn.1 rs]
  have cone : R.c ≤ 1 := by nlinarith only [R.unit_normal,sq_nonneg R.s,sq_nonneg (R.c-1)]
  have sone : R.s ≤ 1 := by nlinarith only [R.unit_normal,sq_nonneg R.c,sq_nonneg (R.s-1)]
  have sideR : 1 < R.side := by rwa [←same]
  have top := upper_wall R wall
  have modes := alternatives B R bn rc rs side same minor bands high rA rD apart
  have rFaces : R.loU+R.side ≤ (2/5)*R.c+R.s ∨ R.c-(2/5)*R.s ≤ R.loV := by
    by_cases first : R.loU+R.side ≤ (2/5)*R.c+R.s
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro no
      apply rT
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [rD.1,rA.2.2.2,rc,rs,first,no]
  have lowerFormula := lower_in_bands R B.c B.s
  have upperFormula := upper_in_bands B R.c R.s
  have lu : B.c*R.c+B.s*R.s=alpha := rfl
  have lv : -B.c*R.s+B.s*R.c=-beta := by dsimp [beta]; ring
  have uu : R.c*B.c+R.s*B.s=alpha := by dsimp [alpha]; ring
  have uv : -R.c*B.s+R.s*B.c=beta := by dsimp [beta]; ring
  rw [lu,lv,abs_of_pos ap] at lowerFormula
  rw [uu,uv,abs_of_pos ap] at upperFormula
  have lower_bound (bound : B.loU+B.side ≤ lower R B.c B.s) :
      B.side-B.c ≤ lower R B.c B.s := by
    calc
      _ = -B.c+B.side := by ring
      _ ≤ B.loU+B.side := add_le_add_left bands.1 _
      _ ≤ _ := bound
  rcases rFaces with upperU | lowerV
  · rcases modes with bu | ru
    · by_cases sign : beta ≤ 0
      · rw [abs_of_nonneg (neg_nonneg.mpr sign)] at lowerFormula
        have coords := C981CompletionOppositeSupport.cross_order B.c B.s R.c R.s bp bn.1 rc rs
          bn.2.2 R.unit_normal (by dsimp [beta] at sign; linarith only [sign])
        have first := mul_nonneg ap.le (show 0 ≤ (2/5)*R.c+R.s-R.side-R.loU by linarith only [upperU])
        have last := mul_nonneg (neg_nonneg.mpr sign)
          (show 0 ≤ R.c-(13/50)*R.s-R.loV by linarith only [rD.2.2.1])
        have strict := mul_pos ap (sub_pos.mpr sideR)
        have identity : alpha*((2/5)*R.c+R.s-1)-beta*(R.c-(13/50)*R.s)=
            (2/5)*B.c+B.s-alpha-(7/50)*beta*R.s := by
          dsimp [alpha,beta]
          linear_combination ((2/5)*B.c+B.s)*R.unit_normal
        have cut : 1 < (7/5)*B.c+B.s-alpha-(7/50)*beta*R.s := by
          have difference : alpha*((2/5)*R.c+R.s-1)-beta*(R.c-(13/50)*R.s)-
              lower R B.c B.s =
              alpha*((2/5)*R.c+R.s-R.side-R.loU)+
                (-beta)*(R.c-(13/50)*R.s-R.loV)+alpha*(R.side-1) := by
            rw [lowerFormula]
            ring
          have support : lower R B.c B.s <
              alpha*((2/5)*R.c+R.s-1)-beta*(R.c-(13/50)*R.s) := by
            apply sub_pos.mp
            rw [difference]
            exact add_pos_of_nonneg_of_pos (add_nonneg first last) strict
          have result := lt_trans
            (lt_of_lt_of_le (sub_lt_sub_right side B.c) (lower_bound bu)) support
          rw [identity] at result
          have shifted := add_lt_add_right result B.c
          convert shifted using 1 <;> ring
        have cWeight := mul_nonneg (show 0 ≤ 1-B.c by linarith only [(normal_bounds bn).2.1])
          (sub_nonneg.mpr cone)
        have sWeight := mul_nonneg rs (sub_nonneg.mpr coords.2)
        have arcWeight := mul_nonneg rc.le (sub_nonneg.mpr cone)
        have alphaLower : B.c ≤ alpha := by
          dsimp [alpha]
          nlinarith only [cWeight,sWeight,arcWeight,R.unit_normal]
        have delta : -beta ≤ B.s := by
          have one := mul_nonneg bn.1 (sub_nonneg.mpr cone)
          have two := mul_nonneg bp.le rs
          dsimp [beta]
          nlinarith only [one,two]
        have bound : -beta*R.s ≤ 1/4 := by
          calc
            _ ≤ (1/2)*(1/2) := mul_le_mul (le_trans delta minor.tHigh)
              (le_trans coords.2 minor.tHigh) rs (by norm_num : (0:ℝ)≤1/2)
            _ = _ := by norm_num
        have endpoint : (7/5)*B.c+B.s-alpha-(7/50)*beta*R.s ≤ 1 := by
          calc
            _ = (2/5)*B.c+B.s+(B.c-alpha)+(7/50)*(-beta*R.s) := by ring
            _ ≤ (2/5)*B.c+B.s+0+(7/50)*(1/4) :=
              add_le_add (add_le_add_right (sub_nonpos.mpr alphaLower) _)
                (mul_le_mul_of_nonneg_left bound (by norm_num))
            _ = (2/5)*B.c+B.s+(7/50)*(1/4) := by ring
            _ ≤ (2/5)*(883/1000)+1/2+(7/50)*(1/4) :=
              add_le_add_left
                (add_le_add (mul_le_mul_of_nonneg_left minor.bHigh.le (by norm_num)) minor.tHigh) _
            _ ≤ 1 := by norm_num
        exact (not_lt_of_ge endpoint) cut
      · have sign' : 0 ≤ beta := le_of_lt (lt_of_not_ge sign)
        rw [abs_of_nonpos (neg_nonpos.mpr sign')] at lowerFormula
        have first := mul_nonneg ap.le (show 0 ≤ (2/5)*R.c+R.s-R.side-R.loU by linarith only [upperU])
        have last := mul_nonneg sign'
          (show 0 ≤ R.loV+R.side-R.c-(2/5)*R.s by linarith only [rA.2.2.2])
        have strict := mul_pos ap (sub_pos.mpr sideR)
        have identity : alpha*((2/5)*R.c+R.s-1)-beta*(R.c+(2/5)*R.s)=
            (2/5)*B.c+B.s-alpha-(4/5)*beta*R.s := by
          dsimp [alpha,beta]
          linear_combination ((2/5)*B.c+B.s)*R.unit_normal
        have cut : 1 < (7/5)*B.c+B.s-alpha-(4/5)*beta*R.s := by
          have difference : alpha*((2/5)*R.c+R.s-1)-beta*(R.c+(2/5)*R.s)-
              lower R B.c B.s =
              alpha*((2/5)*R.c+R.s-R.side-R.loU)+
                beta*(R.loV+R.side-R.c-(2/5)*R.s)+alpha*(R.side-1) := by
            rw [lowerFormula]
            ring
          have support : lower R B.c B.s <
              alpha*((2/5)*R.c+R.s-1)-beta*(R.c+(2/5)*R.s) := by
            apply sub_pos.mp
            rw [difference]
            exact add_pos_of_nonneg_of_pos (add_nonneg first last) strict
          have result := lt_trans
            (lt_of_lt_of_le (sub_lt_sub_right side B.c) (lower_bound bu)) support
          rw [identity] at result
          have shifted := add_lt_add_right result B.c
          convert shifted using 1 <;> ring
        have coords := C981CompletionOppositeSupport.cross_order R.c R.s B.c B.s rc rs bp bn.1
          R.unit_normal bn.2.2 (by dsimp [beta] at sign'; linarith only [sign'])
        let F := 7/5-R.c-(4/5)*R.s^2
        let G := 1-R.s+(4/5)*R.c*R.s
        have fUpper : F ≤ 3/5 := by
          have product := mul_nonneg rc.le (show 0 ≤ 1-(4/5)*R.c by linarith only [cone])
          dsimp [F]
          nlinarith only [product,R.unit_normal]
        have gUpper : G ≤ 453/500 := by
          have product := mul_nonneg rs (sub_nonneg.mpr cone)
          dsimp [G]
          nlinarith only [product,coords.2,minor.tLow]
        have exactCut : 1 < B.c*F+B.s*G := by
          dsimp [F,G,alpha,beta] at cut ⊢
          nlinarith only [cut]
        have endpoint : B.c*F+B.s*G ≤ 1 := by
          calc
            _ ≤ B.c*(3/5)+B.s*(453/500) :=
              add_le_add (mul_le_mul_of_nonneg_left fUpper bp.le)
                (mul_le_mul_of_nonneg_left gUpper bn.1)
            _ ≤ (883/1000)*(3/5)+(1/2)*(453/500) :=
              add_le_add (mul_le_mul_of_nonneg_right minor.bHigh.le (by norm_num))
                (mul_le_mul_of_nonneg_right minor.tHigh (by norm_num))
            _ ≤ 1 := by norm_num
        exact (not_lt_of_ge endpoint) exactCut
    · have own := (strict_bounds B _ _ R.c R.s R.unit_normal marker).2
      have short := (short_projections R (3/4) (13/20) (by norm_num)).2.1
      nlinarith only [ru,own,upperU,short,sideR]
  · have sp : 0 < R.s := by
      apply lt_of_not_ge
      intro no
      have zero : R.s=0 := le_antisymm no rs
      have one : R.c=1 := by nlinarith only [R.unit_normal,rc,zero,sq_nonneg (R.c-1)]
      rw [zero,one] at lowerV top
      norm_num at lowerV top
      linarith only [lowerV,top,sideR]
    by_cases sign : beta ≤ 0
    · rw [abs_of_nonneg (neg_nonneg.mpr sign)] at lowerFormula
      rw [abs_of_nonpos sign] at upperFormula
      rcases modes with bu | ru
      · have exactLower : lower R B.c B.s=alpha*R.loU-beta*R.loV := by
          rw [lowerFormula]
          ring
        have necessary := lower_bound bu
        rw [exactLower] at necessary
        have one := mul_nonneg sp.le (sub_nonneg.mpr necessary)
        have two := mul_nonneg ap.le (show 0 ≤ 2-R.s*(R.loU+R.side)-R.c*(R.loV+R.side) by linarith only [top])
        have three := mul_nonneg bp.le (sub_nonneg.mpr lowerV)
        have coefficient : 0 < R.s+alpha*(R.c+R.s) := by
          nlinarith only [sp,mul_pos ap (show 0 < R.c+R.s by linarith only [rc,rs])]
        have strict := mul_pos coefficient (sub_pos.mpr sideR)
        have identity : R.s*(alpha*R.loU-beta*R.loV-(R.side-B.c))+
            alpha*(2-R.s*(R.loU+R.side)-R.c*(R.loV+R.side))+
            B.c*(R.loV-(R.c-(2/5)*R.s)) =
            2*alpha-B.c*R.c+(7/5)*B.c*R.s-R.side*(R.s+alpha*(R.c+R.s)) := by
          dsimp [alpha,beta]
          linear_combination -B.c*R.loV*R.unit_normal
        have cut : 0 < 2*alpha-B.c*R.c+(7/5)*B.c*R.s-R.s-alpha*(R.c+R.s) := by
          rw [same] at one
          have total := add_nonneg (add_nonneg one two) three
          rw [identity] at total
          have result := add_pos_of_nonneg_of_pos total strict
          convert result using 1; ring
        exact bu_negative R.c R.s B.c B.s R.unit_normal rc sp bn minor
          (by dsimp [beta] at sign; exact sign) (by dsimp [alpha] at cut; exact cut)
      · have one := mul_nonneg ap.le (sub_nonneg.mpr bands.1)
        have two := mul_nonneg (neg_nonneg.mpr sign)
          (show 0 ≤ B.c+B.s-B.side-B.loV by linarith only [bands.2.2.2])
        have bound : alpha*(R.side-B.c)+beta*(B.c+B.s-R.side) ≤ R.loU := by
          have difference : upper B R.c R.s-
              (alpha*(R.side-B.c)+beta*(B.c+B.s-R.side)) =
              alpha*(B.loU- -B.c)+(-beta)*(B.c+B.s-B.side-B.loV) := by
            rw [upperFormula,←same]
            ring
          apply le_trans _ ru
          apply sub_nonneg.mp
          rw [difference]
          exact add_nonneg one two
        have uWeight := mul_nonneg sp.le (sub_nonneg.mpr bound)
        have vWeight := mul_nonneg rc.le (sub_nonneg.mpr lowerV)
        have coefficient : 0 < R.s*(alpha-beta)+R.c+R.s := by
          have product := mul_nonneg rs (show 0 ≤ alpha-beta by linarith only [ap,sign])
          linarith only [product,rc,rs]
        have strict := mul_pos coefficient (sub_pos.mpr sideR)
        have positive := ru_negative R.c R.s B.c B.s R.unit_normal rc sp bn minor
          (by dsimp [beta] at sign; exact sign)
        dsimp [alpha,beta] at uWeight vWeight strict positive
        nlinarith only [top,uWeight,vWeight,strict,positive]
    · have sign' : 0 ≤ beta := le_of_lt (lt_of_not_ge sign)
      rw [abs_of_nonpos (neg_nonpos.mpr sign')] at lowerFormula
      rw [abs_of_nonneg sign'] at upperFormula
      rcases modes with bu | ru
      · have exactLower : lower R B.c B.s=alpha*R.loU-beta*(R.loV+R.side) := by
          rw [lowerFormula]
          ring
        have necessary := lower_bound bu
        rw [exactLower] at necessary
        have one := mul_nonneg sp.le (sub_nonneg.mpr necessary)
        have two := mul_nonneg ap.le (show 0 ≤ 2-R.s*(R.loU+R.side)-R.c*(R.loV+R.side) by linarith only [top])
        have three := mul_nonneg bp.le (sub_nonneg.mpr lowerV)
        have coefficient : 0 < R.s+alpha*(R.c+R.s)+R.s*beta := by
          have cross := mul_nonneg rs sign'
          nlinarith only [sp,cross,mul_pos ap (show 0 < R.c+R.s by linarith only [rc,rs])]
        have strict := mul_pos coefficient (sub_pos.mpr sideR)
        have identity : R.s*(alpha*R.loU-beta*(R.loV+R.side)-(R.side-B.c))+
            alpha*(2-R.s*(R.loU+R.side)-R.c*(R.loV+R.side))+
            B.c*(R.loV-(R.c-(2/5)*R.s)) =
            2*alpha-B.c*R.c+(7/5)*B.c*R.s-R.side*(R.s+alpha*(R.c+R.s)+R.s*beta) := by
          dsimp [alpha,beta]
          linear_combination -B.c*R.loV*R.unit_normal
        have cut : 0 < 2*alpha-B.c*R.c+(7/5)*B.c*R.s-R.s-alpha*(R.c+R.s)-R.s*beta := by
          rw [same] at one
          have total := add_nonneg (add_nonneg one two) three
          rw [identity] at total
          have result := add_pos_of_nonneg_of_pos total strict
          convert result using 1; ring
        exact bu_positive R.c R.s B.c B.s R.unit_normal rc sp bn minor
          (by dsimp [beta] at sign'; exact sign') (by dsimp [alpha,beta] at cut; exact cut)
      · have one := mul_nonneg ap.le (sub_nonneg.mpr bands.1)
        have two := mul_nonneg sign' (sub_nonneg.mpr bands.2.1)
        have bound : alpha*(R.side-B.c)+beta*(R.side+(2/5)*B.s) ≤ R.loU := by
          have difference : upper B R.c R.s-
              (alpha*(R.side-B.c)+beta*(R.side+(2/5)*B.s)) =
              alpha*(B.loU- -B.c)+beta*(B.loV-(2/5)*B.s) := by
            rw [upperFormula,←same]
            ring
          apply le_trans _ ru
          apply sub_nonneg.mp
          rw [difference]
          exact add_nonneg one two
        have uWeight := mul_nonneg sp.le (sub_nonneg.mpr bound)
        have vWeight := mul_nonneg rc.le (sub_nonneg.mpr lowerV)
        have coefficient : 0 < R.s*(alpha+beta)+R.c+R.s := by
          have product := mul_nonneg rs (show 0 ≤ alpha+beta by linarith only [ap,sign'])
          linarith only [product,rc,rs]
        have strict := mul_pos coefficient (sub_pos.mpr sideR)
        have positive := ru_positive R.c R.s B.c B.s R.unit_normal rc sp bn minor
        dsimp [alpha,beta] at uWeight vWeight strict positive
        nlinarith only [top,uWeight,vWeight,strict,positive]

theorem angle (B R : OpenSquare) (bn : Normal B.c B.s)
    (side : 1 < B.side) (same : B.side=R.side)
    (marker : B.Inside (-(7/20)) (7/20))
    (low : B.Inside (-1) (13/50)) (high : B.Inside (-1) (2/5))
    (missingLow : ¬ B.Inside (-1) 0) (missingInner : ¬ B.Inside (-(2/5)) 0)
    (missingCorner : ¬ B.Inside (-1) 1) (missingTop : ¬ B.Inside (-(2/5)) 1)
    (wall : ∀ x y, R.Inside x y → y ≤ 2)
    (rA : R.Inside (-(2/5)) 1) (rD : R.Inside (13/50) 1)
    (rT : ¬ R.Inside (2/5) 1)
    (apart : ∀ x y, ¬ (B.Inside x y ∧ R.Inside x y)) : 1/2 < B.s := by
  apply lt_of_not_ge
  intro small
  have bands := faces B bn side marker low high missingLow missingInner missingCorner missingTop
  have span : 1 < B.s+(3/5)*B.c := by linarith only [bands.1,bands.2.2.1,side]
  have minor := minor bn span small
  obtain ⟨Q,hc,hs,shape,equivalent,_⟩ := ClosedFrames.positive_frame R
  have same' : B.side=Q.side := same.trans shape.symm
  have qWall : ∀ x y, Q.Inside x y → y ≤ 2 := fun x y h => wall x y ((equivalent _ _).mp h)
  have qApart : ∀ x y, ¬ (B.Inside x y ∧ Q.Inside x y) := by
    intro x y h
    exact apart x y ⟨h.1,(equivalent _ _).mp h.2⟩
  exact positive B Q bn hc hs side same' minor bands marker high qWall
    ((equivalent _ _).mpr rA) ((equivalent _ _).mpr rD)
    (fun h => rT ((equivalent _ _).mp h)) qApart

#print axioms angle
end N12Compact.C981CompletionLastRightWall
