import Compact.Completion.C981.ShortRows.CoreScalars
import Compact.Geometry.ABTransverse
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! A central four-diamond owner and its actual southeast neighbor.
The corner point and the advanced wall point are genuine foreign strict
points. Missing points and separating axes retain boundary equality. -/
namespace N12Compact.C981CompletionShortSqueeze
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic
open C977ChainBridge
open C981CompletionShortScalars
set_option Elab.async false

private theorem corner (q : OpenSquare) (U V : ℝ)
    (hu : q.loU ≤ U ∧ U ≤ q.loU+q.side)
    (hv : q.loV ≤ V ∧ V ≤ q.loV+q.side) :
    ClosedInside q (q.c*U-q.s*V) (q.s*U+q.c*V) := by
  have first : q.c*(q.c*U-q.s*V)+q.s*(q.s*U+q.c*V)=U := by
    linear_combination U*q.unit_normal
  have last : -q.s*(q.c*U-q.s*V)+q.c*(q.s*U+q.c*V)=V := by
    linear_combination V*q.unit_normal
  change q.loU ≤ _ ∧ _ ≤ q.loU+q.side ∧ q.loV ≤ _ ∧ _ ≤ q.loV+q.side
  rw [first,last]; exact ⟨hu.1,hu.2,hv.1,hv.2⟩

private theorem project_upper (q : OpenSquare) (nx ny U V : ℝ)
    (hu : q.loU ≤ U ∧ U ≤ q.loU+q.side)
    (hv : q.loV ≤ V ∧ V ≤ q.loV+q.side) :
    (nx*q.c+ny*q.s)*U+(-nx*q.s+ny*q.c)*V ≤ upper q nx ny := by
  have bound := (closed_bounds q _ _ nx ny (corner q U V hu hv)).2
  convert bound using 1 <;> ring

private theorem project_lower (q : OpenSquare) (nx ny U V : ℝ)
    (hu : q.loU ≤ U ∧ U ≤ q.loU+q.side)
    (hv : q.loV ≤ V ∧ V ≤ q.loV+q.side) :
    lower q nx ny ≤ (nx*q.c+ny*q.s)*U+(-nx*q.s+ny*q.c)*V := by
  have bound := (closed_bounds q _ _ nx ny (corner q U V hu hv)).1
  convert bound using 1 <;> ring

theorem core_faces (A : OpenSquare) (side : 1 < A.side)
    (normal : Normal A.c A.s)
    (left : A.Inside (87/50) 2) (bottom : A.Inside 2 (87/50))
    (marker : A.Inside (47/20) (47/20))
    (missingNW : ¬ A.Inside (33/20) (47/20))
    (missingSE : ¬ A.Inside (47/20) (33/20)) :
    Core A.c A.s ∧
      (33/20)*A.c+(47/20)*A.s ≤ A.loU ∧
      (33/20)*A.c-(47/20)*A.s ≤ A.loV := by
  have bounds := normal_bounds normal
  have cp : 0 < A.c := by linarith only [bounds.1]
  have lowerV : (33/20)*A.c-(47/20)*A.s ≤ A.loV := by
    apply le_of_not_gt
    intro low
    apply missingSE
    refine ⟨?_,?_,by linarith only [low],?_⟩
    · nlinarith only [left.1,normal.2.1,cp]
    · nlinarith only [marker.2.1,normal.1]
    · nlinarith only [marker.2.2.2,cp]
  have short := (short_projections A (7/10) (7/10) (by norm_num)).2.1
  have lowerU : (33/20)*A.c+(47/20)*A.s ≤ A.loU := by
    apply le_of_not_gt
    intro low
    apply missingNW
    refine ⟨by linarith only [low],?_,?_,?_⟩
    · nlinarith only [marker.2.1,cp]
    · nlinarith only [bottom.2.2.1,normal.1,cp]
    · linarith only [lowerV,short,side]
  have narrow : 35*A.s ≤ 9*A.c := by linarith only [lowerU,left.1]
  exact ⟨core_bounds normal narrow,lowerU,lowerV⟩

private theorem coefficient_positive (c s b t : ℝ) (core : Core c s)
    (bp : 0 < b) (canon : -b ≤ t) : 0 < c*b+s*t := by
  have one := mul_nonneg core.2.2.1 (show 0 ≤ t+b by linarith only [canon])
  have two := mul_pos bp (show 0 < c-s by linarith only [core.1,core.2.2.2.1])
  nlinarith only [one,two]

private theorem corner_faces (B : OpenSquare) (bp : 0 < B.c) (canon : |B.s| ≤ B.c)
    (marker : B.Inside (47/20) (33/20)) (right : B.Inside 3 (87/50))
    (missing : ¬ B.Inside 3 1) :
    B.loU+B.side ≤ 3*B.c+B.s ∨ B.c-3*B.s ≤ B.loV := by
  have signs := abs_le.mp canon
  have ulo : B.loU < 3*B.c+B.s := by nlinarith only [marker.1,signs.2,bp]
  have vhi : B.c-3*B.s < B.loV+B.side := by linarith only [right.2.2.2,bp]
  by_cases uhi : B.loU+B.side ≤ 3*B.c+B.s
  · exact Or.inl uhi
  · exact Or.inr (le_of_not_gt (fun vlo => missing
      ⟨by linarith only [ulo],by linarith only [uhi],
        by linarith only [vlo],by linarith only [vhi]⟩))

private theorem positive_corner_low (B : OpenSquare) (positive : 0 ≤ B.s)
    (right : B.Inside 3 (87/50)) (faces :
      B.loU+B.side ≤ 3*B.c+B.s ∨ B.c-3*B.s ≤ B.loV) :
    B.c-3*B.s ≤ B.loV := by
  rcases faces with upper | lower
  · exfalso; linarith only [upper,right.2.1,positive]
  · exact lower

private theorem advanced_faces (B : OpenSquare) (bp : 0 < B.c)
    (canon : |B.s| ≤ B.c) (marker : B.Inside (47/20) (33/20))
    (right : B.Inside 3 (87/50)) (missing : ¬ B.Inside (14/5) 1)
    (negative : B.s ≤ 0) (small : -B.s < (10/37)*B.c)
    (cap : B.loU+B.side ≤ 3*B.c+B.s) (side : 1 < B.side) :
    B.c-(14/5)*B.s ≤ B.loV := by
  have bc1 : B.c ≤ 1 := by nlinarith only [B.unit_normal,sq_nonneg B.s,sq_nonneg (B.c-1)]
  have ulo : B.loU < (14/5)*B.c+B.s := by linarith only [cap,side,bc1]
  have uhi : (14/5)*B.c+B.s < B.loU+B.side := by linarith only [right.2.1,small,bp]
  have vhi : B.c-(14/5)*B.s < B.loV+B.side := by
    nlinarith only [marker.2.2.2,(abs_le.mp canon).1,bp]
  exact le_of_not_gt (fun vlo => missing
    ⟨by linarith only [ulo],by linarith only [uhi],
      by linarith only [vlo],by linarith only [vhi]⟩)

private theorem positive_advanced_modes (B : OpenSquare) (bp : 0 < B.c)
    (positive : 0 ≤ B.s) (marker : B.Inside (47/20) (33/20))
    (right : B.Inside 3 (87/50)) (missing : ¬ B.Inside (14/5) 1) :
    (14/5)*B.c+B.s ≤ B.loU ∨ B.c-(14/5)*B.s ≤ B.loV := by
  have uhi : (14/5)*B.c+B.s < B.loU+B.side := by nlinarith only [right.2.1,bp,positive]
  have vhi : B.c-(14/5)*B.s < B.loV+B.side := by nlinarith only [marker.2.2.2,bp,positive]
  by_cases ulo : (14/5)*B.c+B.s ≤ B.loU
  · exact Or.inl ulo
  · exact Or.inr (le_of_not_gt (fun vlo => missing
      ⟨by linarith only [ulo],by linarith only [uhi],
        by linarith only [vlo],by linarith only [vhi]⟩))

private theorem axes (A B : OpenSquare) (side : 1 < A.side) (same : A.side=B.side)
    (normal : Normal A.c A.s) (bp : 0 < B.c) (canon : |B.s| ≤ B.c)
    (loU : (33/20)*A.c+(47/20)*A.s ≤ A.loU)
    (bottom : A.Inside 2 (87/50)) (marker : A.Inside (47/20) (47/20))
    (bMarker : B.Inside (47/20) (33/20))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)) :
    upper B (-A.s) A.c ≤ A.loV ∨
      (B.s ≤ 0 ∧ upper A B.c B.s ≤ B.loU) ∨
      B.loV+B.side ≤ lower A (-B.s) B.c := by
  have ac : 0 < A.c := by linarith only [(normal_bounds normal).1]
  have short := (short_projections A (7/10) (-(7/10)) (by norm_num)).2.1
  have all := CongruentSAT.faceSeparation_of_disjoint A B same apart
  change pairRadius A B ≤ |A.c*(centerX B-centerX A)+A.s*(centerY B-centerY A)| ∨
    pairRadius A B ≤ |-A.s*(centerX B-centerX A)+A.c*(centerY B-centerY A)| ∨
    pairRadius B A ≤ |B.c*(centerX B-centerX A)+B.s*(centerY B-centerY A)| ∨
    pairRadius B A ≤ |-B.s*(centerX B-centerX A)+B.c*(centerY B-centerY A)| at all
  have separate (nx ny r : ℝ) (identity : supportRadius A nx ny+supportRadius B nx ny=r)
      (h : r ≤ |nx*(centerX B-centerX A)+ny*(centerY B-centerY A)|) :=
    separated A B nx ny (by rwa [identity])
  rcases all with au | av | bu | bv
  · rcases separate _ _ _ (parallel_radius A B) au with forward | reverse
    · have bpnt := (strict_bounds B _ _ A.c A.s A.unit_normal bMarker).1
      rw [(ownU A).2] at forward
      exfalso; linarith only [forward,bpnt,loU,side,short]
    · have apnt := (strict_bounds A _ _ A.c A.s A.unit_normal bottom).1
      have bpnt := (strict_bounds B _ _ A.c A.s A.unit_normal bMarker).2
      exfalso; nlinarith only [reverse,apnt,bpnt,ac,normal.2.1]
  · have unit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    rcases separate _ _ _ (transverse_radius A B) av with forward | reverse
    · have apnt := (strict_bounds A _ _ (-A.s) A.c unit marker).2
      have bpnt := (strict_bounds B _ _ (-A.s) A.c unit bMarker).1
      exfalso; nlinarith only [forward,apnt,bpnt,ac]
    · exact Or.inl (by simpa only [(ownV A).1] using reverse)
  · have identity : supportRadius A B.c B.s+supportRadius B B.c B.s=pairRadius B A := by
      rw [add_comm]; exact parallel_radius B A
    rcases separate _ _ _ identity bu with forward | reverse
    · by_cases sign : 0 ≤ B.s
      · have apnt := (strict_bounds A _ _ B.c B.s B.unit_normal marker).2
        have bpnt := (strict_bounds B _ _ B.c B.s B.unit_normal bMarker).1
        exfalso; nlinarith only [forward,apnt,bpnt,sign]
      · exact Or.inr (Or.inl ⟨(lt_of_not_ge sign).le,by simpa only [(ownU B).1] using forward⟩)
    · have apnt := (strict_bounds A _ _ B.c B.s B.unit_normal bottom).1
      have bpnt := (strict_bounds B _ _ B.c B.s B.unit_normal bMarker).2
      exfalso; nlinarith only [reverse,apnt,bpnt,bp,(abs_le.mp canon).2]
  · have identity : supportRadius A (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B A := by
      rw [add_comm]; exact transverse_radius B A
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    rcases separate _ _ _ identity bv with forward | reverse
    · have apnt := (strict_bounds A _ _ (-B.s) B.c unit marker).2
      have bpnt := (strict_bounds B _ _ (-B.s) B.c unit bMarker).1
      exfalso; nlinarith only [forward,apnt,bpnt,bp]
    · exact Or.inr (Or.inr (by simpa only [(ownV B).2] using reverse))

private theorem backward_impossible (A B : OpenSquare) (side : 1 < A.side)
    (core : Core A.c A.s) (bp : 0 < B.c) (canon : |B.s| ≤ B.c)
    (negative : B.s ≤ 0) (loU : (33/20)*A.c+(47/20)*A.s ≤ A.loU)
    (bottom : A.Inside 2 (87/50)) (bMarker : B.Inside (47/20) (33/20))
    (axis : upper A B.c B.s ≤ B.loU) : False := by
  let alpha := A.c*B.c+A.s*B.s
  let beta := -A.s*B.c+A.c*B.s
  have ap : 0 < alpha := coefficient_positive _ _ _ _ core bp (abs_le.mp canon).1
  have bn : beta ≤ 0 := by
    dsimp [beta]; nlinarith only [mul_nonpos_of_nonneg_of_nonpos
      (show 0 ≤ A.c by linarith only [core.1]) negative,
      mul_nonneg core.2.2.1 bp.le]
  have point := project_upper A B.c B.s (A.loU+A.side) A.loV
    ⟨by linarith only [A.side_pos],le_rfl⟩ ⟨le_rfl,by linarith only [A.side_pos]⟩
  have u := mul_nonneg ap.le (show 0 ≤ A.loU+A.side-((33/20)*A.c+(47/20)*A.s+1) by
    linarith only [loU,side])
  have v := mul_nonneg (neg_nonneg.mpr bn)
    (show 0 ≤ (87/50)*A.c-2*A.s-A.loV by linarith only [bottom.2.2.1])
  have identity : alpha*((33/20)*A.c+(47/20)*A.s+1)+beta*((87/50)*A.c-2*A.s)-
      ((47/20)*B.c+(33/20)*B.s)=
      B.c*(A.c-7/10+(7/20)*A.s^2+(61/100)*A.c*A.s)+
        B.s*(A.s+9/100+(61/100)*A.s^2-(7/20)*A.c*A.s) := by
    dsimp [alpha,beta]; linear_combination ((33/20)*B.c+(87/50)*B.s)*A.unit_normal
  have margin := backward_u core bp negative (abs_le.mp canon).1
  dsimp [alpha,beta] at u v
  nlinarith only [point,u,v,identity,margin,axis,bMarker.1]

private theorem own_v_impossible (A B : OpenSquare) (side : 1 < B.side) (aside : 1 < A.side)
    (core : Core A.c A.s) (bp : 0 < B.c) (canon : |B.s| ≤ B.c)
    (loU : (33/20)*A.c+(47/20)*A.s ≤ A.loU)
    (left : A.Inside (87/50) 2) (bottom : A.Inside 2 (87/50))
    (bMarker : B.Inside (47/20) (33/20)) (right : B.Inside 3 (87/50))
    (cornerMissing : ¬ B.Inside 3 1) (wallMissing : ¬ B.Inside (14/5) 1)
    (axis : B.loV+B.side ≤ lower A (-B.s) B.c) : False := by
  have ac : 0 < A.c := by linarith only [core.1]
  have bc1 : B.c ≤ 1 := by nlinarith only [B.unit_normal,sq_nonneg B.s,sq_nonneg (B.c-1)]
  have faces := corner_faces B bp canon bMarker right cornerMissing
  have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
  have target := (strict_bounds A _ _ (-B.s) B.c unit bottom).1
  by_cases sign : 0 ≤ B.s
  · have normal : Normal B.c B.s := ⟨sign,(abs_le.mp canon).2,B.unit_normal⟩
    have low := positive_corner_low B sign right faces
    let gamma := A.s*B.c-A.c*B.s
    let alpha := A.c*B.c+A.s*B.s
    have ap : 0 < alpha := coefficient_positive _ _ _ _ core bp (abs_le.mp canon).1
    by_cases order : 0 ≤ gamma
    · have bound : B.s ≤ (9/35)*B.c := by
        have product := mul_nonneg bp.le (show 0 ≤ (9/35)*A.c-A.s by linarith only [core.2.2.2.2])
        dsimp [gamma] at order
        apply (mul_le_mul_left ac).mp
        nlinarith only [product,order]
      linarith only [axis,target,low,side,bound,bc1]
    · have gn : gamma ≤ 0 := (lt_of_not_ge order).le
      have point := project_lower A (-B.s) B.c (A.loU+A.side) A.loV
        ⟨by linarith only [A.side_pos],le_rfl⟩ ⟨le_rfl,by linarith only [A.side_pos]⟩
      have u := mul_nonneg (neg_nonneg.mpr gn)
        (show 0 ≤ A.loU+A.side-((33/20)*A.c+(47/20)*A.s+1) by linarith only [loU,aside])
      have v := mul_nonneg ap.le
        (show 0 ≤ (87/50)*A.c-2*A.s-A.loV by linarith only [bottom.2.2.1])
      have identity : gamma*((33/20)*A.c+(47/20)*A.s+1)+alpha*((87/50)*A.c-2*A.s)-
          (B.c-3*B.s)=
          B.c*(37/50+(61/100)*A.s^2-(7/20)*A.c*A.s+A.s)+
            B.s*(27/20-(7/20)*A.s^2-(61/100)*A.c*A.s-A.c) := by
        dsimp [gamma,alpha]; linear_combination ((87/50)*B.c-(33/20)*B.s)*A.unit_normal
      have margin := positive_own_v core normal
      dsimp [gamma,alpha] at u v
      nlinarith only [point,u,v,identity,margin,axis,low,side]
  · have negative : B.s ≤ 0 := (lt_of_not_ge sign).le
    have bpoint := (strict_bounds B _ _ (-B.s) B.c unit bMarker).2
    rw [(ownV B).2] at bpoint
    have narrow : -B.s < (9/35)*B.c := by linarith only [axis,target,bpoint]
    rcases faces with cap | low
    · have advanced := advanced_faces B bp canon bMarker right wallMissing negative
        (by linarith only [narrow,bp]) cap side
      linarith only [axis,target,advanced,side,negative,bc1]
    · linarith only [axis,target,low,side,negative,bc1]

private theorem a_v_impossible (A B : OpenSquare) (side : 1 < B.side)
    (core : Core A.c A.s) (bp : 0 < B.c) (canon : |B.s| ≤ B.c)
    (bottom : A.Inside 2 (87/50)) (bMarker : B.Inside (47/20) (33/20))
    (right : B.Inside 3 (87/50)) (cornerMissing : ¬ B.Inside 3 1)
    (wallMissing : ¬ B.Inside (14/5) 1)
    (axis : upper B (-A.s) A.c ≤ A.loV) : False := by
  let gamma := A.c*B.s-A.s*B.c
  let alpha := A.c*B.c+A.s*B.s
  have ap : 0 < alpha := coefficient_positive _ _ _ _ core bp (abs_le.mp canon).1
  have faces := corner_faces B bp canon bMarker right cornerMissing
  have low_corner (gn : gamma ≤ 0) := project_upper B (-A.s) A.c B.loU (B.loV+B.side)
    ⟨le_rfl,by linarith only [B.side_pos]⟩ ⟨by linarith only [B.side_pos],le_rfl⟩
  have high_corner (gp : 0 ≤ gamma) := project_upper B (-A.s) A.c (B.loU+B.side) (B.loV+B.side)
    ⟨by linarith only [B.side_pos],le_rfl⟩ ⟨by linarith only [B.side_pos],le_rfl⟩
  have advanced_low (gn : gamma ≤ 0) (low : B.c-(14/5)*B.s ≤ B.loV)
      (margin : 0 < gamma*((47/20)*B.c+(33/20)*B.s)+
        alpha*(B.c-(14/5)*B.s+1)-((87/50)*A.c-2*A.s)) : False := by
    have point := low_corner gn
    have u := mul_nonneg (neg_nonneg.mpr gn)
      (show 0 ≤ (47/20)*B.c+(33/20)*B.s-B.loU by linarith only [bMarker.1])
    have v := mul_nonneg ap.le (show 0 ≤ B.loV+B.side-(B.c-(14/5)*B.s+1) by
      linarith only [low,side])
    dsimp [gamma,alpha] at u v
    nlinarith only [point,u,v,margin,axis,bottom.2.2.1]
  by_cases sign : 0 ≤ B.s
  · have normal : Normal B.c B.s := ⟨sign,(abs_le.mp canon).2,B.unit_normal⟩
    have low := positive_corner_low B sign right faces
    by_cases negativeGamma : gamma ≤ 0
    · have small : B.s ≤ 13/50 := by
        have product := mul_nonneg bp.le (show 0 ≤ (9/35)*A.c-A.s by linarith only [core.2.2.2.2])
        have ac : 0 < A.c := by linarith only [core.1]
        have bc1 := (normal_bounds normal).2.1
        dsimp [gamma] at negativeGamma
        have bound : B.s ≤ (9/35)*B.c := by
          apply (mul_le_mul_left ac).mp
          nlinarith only [product,negativeGamma]
        linarith only [bound,bc1]
      have point := low_corner negativeGamma
      have u := mul_nonneg (neg_nonneg.mpr negativeGamma)
        (show 0 ≤ (47/20)*B.c+(33/20)*B.s-B.loU by linarith only [bMarker.1])
      have v := mul_nonneg ap.le (show 0 ≤ B.loV+B.side-(B.c-3*B.s+1) by linarith only [low,side])
      have identity : gamma*((47/20)*B.c+(33/20)*B.s)+alpha*(B.c-3*B.s+1)-
          ((87/50)*A.c-2*A.s)=
          A.c*(B.c-37/50+(13/20)*B.s^2-(13/20)*B.c*B.s)+
            A.s*(-7/20-(13/20)*B.s^2-(13/20)*B.c*B.s+B.s) := by
        dsimp [gamma,alpha]; linear_combination (A.c-(47/20)*A.s)*B.unit_normal
      have margin := positive_small core normal small
      dsimp [gamma,alpha] at u v
      nlinarith only [point,u,v,identity,margin,axis,bottom.2.2.1]
    · have gp : 0 ≤ gamma := (lt_of_not_ge negativeGamma).le
      have point := high_corner gp
      rcases positive_advanced_modes B bp sign bMarker right wallMissing with uLow | vLow
      · have u := mul_nonneg gp (show 0 ≤ B.loU+B.side-((14/5)*B.c+B.s+1) by linarith only [uLow,side])
        have v := mul_nonneg ap.le (show 0 ≤ B.loV+B.side-(B.c-3*B.s+1) by linarith only [low,side])
        have identity : gamma*((14/5)*B.c+B.s+1)+alpha*(B.c-3*B.s+1)-
            ((87/50)*A.c-2*A.s)=
            A.c*(B.c+B.s-37/50-(1/5)*B.c*B.s)+
              A.s*(-4/5-(1/5)*B.s^2-B.c+B.s) := by
          dsimp [gamma,alpha]; linear_combination (A.c-(14/5)*A.s)*B.unit_normal
        have margin := positive_lower_u core normal (by simpa [gamma] using gp)
        dsimp [gamma,alpha] at u v
        nlinarith only [point,u,v,identity,margin,axis,bottom.2.2.1]
      · have u := mul_nonneg gp (show 0 ≤ B.loU+B.side-((47/20)*B.c+(33/20)*B.s) by
          linarith only [bMarker.2.1])
        have v := mul_nonneg ap.le (show 0 ≤ B.loV+B.side-(B.c-(14/5)*B.s+1) by linarith only [vLow,side])
        have identity : gamma*((47/20)*B.c+(33/20)*B.s)+alpha*(B.c-(14/5)*B.s+1)-
            ((87/50)*A.c-2*A.s)=
            A.c*(B.c-37/50+(13/20)*B.s^2-(9/20)*B.c*B.s)+
              A.s*(-7/20-(9/20)*B.s^2-(13/20)*B.c*B.s+B.s) := by
          dsimp [gamma,alpha]; linear_combination (A.c-(47/20)*A.s)*B.unit_normal
        have margin := positive_low core normal
        dsimp [gamma,alpha] at u v
        nlinarith only [point,u,v,identity,margin,axis,bottom.2.2.1]
  · let u := -B.s
    have us : B.s = -u := by dsimp [u]; ring
    have negative : B.s ≤ 0 := (lt_of_not_ge sign).le
    have normal : Normal B.c u := ⟨by dsimp [u]; linarith only [negative],
      by dsimp [u]; linarith only [(abs_le.mp canon).1],by dsimp [u]; nlinarith only [B.unit_normal]⟩
    have gn : gamma ≤ 0 := by
      dsimp [gamma]; nlinarith only [mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ A.c by linarith only [core.1]) negative,
        mul_nonneg core.2.2.1 bp.le]
    have low_impossible (low : B.c-(14/5)*B.s ≤ B.loV) : False := by
      apply advanced_low gn low
      have identity : gamma*((47/20)*B.c+(33/20)*B.s)+alpha*(B.c-(14/5)*B.s+1)-
          ((87/50)*A.c-2*A.s)=
          A.c*(B.c-37/50+(13/20)*u^2+(9/20)*B.c*u)+
            A.s*(-7/20-(9/20)*u^2+(13/20)*B.c*u-u) := by
        dsimp [gamma,alpha]; rw [us]
        linear_combination (A.c-(47/20)*A.s)*normal.2.2
      rw [identity]; exact negative_low core normal
    rcases faces with cap | low
    · by_cases steep : (10/37)*B.c ≤ u
      · have point := low_corner gn
        have uw := mul_nonneg (neg_nonneg.mpr gn)
          (show 0 ≤ (47/20)*B.c+(33/20)*B.s-B.loU by linarith only [bMarker.1])
        have vw := mul_nonneg ap.le
          (show 0 ≤ B.loV+B.side-((87/50)*B.c-3*B.s) by linarith only [right.2.2.2])
        have identity : gamma*((47/20)*B.c+(33/20)*B.s)+alpha*((87/50)*B.c-3*B.s)-
            ((87/50)*A.c-2*A.s)=
            A.c*((13/20)*B.c*u-(9/100)*u^2)-
              A.s*(7/20+(13/20)*u^2+(9/100)*B.c*u) := by
          dsimp [gamma,alpha]; rw [us]
          linear_combination ((87/50)*A.c-(47/20)*A.s)*normal.2.2
        have margin := negative_steep core normal steep
        dsimp [gamma,alpha] at uw vw
        nlinarith only [point,uw,vw,identity,margin,axis,bottom.2.2.1]
      · exact low_impossible (advanced_faces B bp canon bMarker right wallMissing negative
          (by dsimp [u] at steep; linarith only [steep]) cap side)
    · exact low_impossible (by linarith only [low,negative])

/-- Every independent canonical frame of the actual neighbor is included.
No upper side cap or containment premise is used in this final squeeze. -/
theorem impossible (A B : OpenSquare) (side : 1 < A.side) (same : A.side=B.side)
    (normal : Normal A.c A.s) (bp : 0 < B.c) (canon : |B.s| ≤ B.c)
    (left : A.Inside (87/50) 2) (bottom : A.Inside 2 (87/50))
    (marker : A.Inside (47/20) (47/20))
    (missingNW : ¬ A.Inside (33/20) (47/20))
    (missingSE : ¬ A.Inside (47/20) (33/20))
    (bMarker : B.Inside (47/20) (33/20)) (right : B.Inside 3 (87/50))
    (cornerMissing : ¬ B.Inside 3 1) (wallMissing : ¬ B.Inside (14/5) 1)
    (apart : ∀ x y, ¬ (A.Inside x y ∧ B.Inside x y)) : False := by
  obtain ⟨core,loU,loV⟩ := core_faces A side normal left bottom marker missingNW missingSE
  have bside : 1 < B.side := by simpa only [same] using side
  rcases axes A B side same normal bp canon loU bottom marker bMarker apart with av | bu | bv
  · exact a_v_impossible A B bside core bp canon bottom bMarker right cornerMissing wallMissing av
  · exact backward_impossible A B side core bp canon bu.1 loU bottom bMarker bu.2
  · exact own_v_impossible A B bside side core bp canon loU left bottom bMarker right cornerMissing wallMissing bv

#print axioms impossible
end N12Compact.C981CompletionShortSqueeze
