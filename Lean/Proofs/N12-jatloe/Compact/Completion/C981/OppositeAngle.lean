import Compact.Completion.C981.OppositeOffset
import Compact.Completion.C981.OppositeSupport

/-! The positive-central angle reduction used in the final C981 cycles.
All coordinate walls below are consequences of the actual excluded whole
segments. The only upper side bound is the original 1001/1000 cap. -/
namespace N12Compact.C981CompletionOppositeAngle

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977ChainBridge
open C981CompletionSupportForms
set_option Elab.async false

private theorem positive_axes (C A : OpenSquare) (r : ℝ) (cs : C.s=r)
    (cn : Normal C.c r) (ac : 0 < A.c) (asign : 0 ≤ A.s)
    (same : C.side=A.side) (center : C.Inside 0 0)
    (north : A.Inside 0 (13/50)) (east : A.Inside (13/50) 0)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ A.Inside x y)) :
    C.loU+C.side ≤ lower A C.c r ∨ upper C A.c A.s ≤ A.loU := by
  have dp : 0 < C.c := by linarith only [(normal_bounds cn).1]
  have all := CongruentSAT.faceSeparation_of_disjoint C A same apart
  change pairRadius C A ≤ |C.c*(centerX A-centerX C)+C.s*(centerY A-centerY C)| ∨
    pairRadius C A ≤ |-C.s*(centerX A-centerX C)+C.c*(centerY A-centerY C)| ∨
    pairRadius A C ≤ |A.c*(centerX A-centerX C)+A.s*(centerY A-centerY C)| ∨
    pairRadius A C ≤ |-A.s*(centerX A-centerX C)+A.c*(centerY A-centerY C)| at all
  have sep (x y R : ℝ) (identity : supportRadius C x y+supportRadius A x y=R)
      (h : R ≤ |x*(centerX A-centerX C)+y*(centerY A-centerY C)|) :=
    separated C A x y (by rwa [identity])
  rcases all with cu | cv | au | av
  · rcases sep _ _ _ (parallel_radius C A) cu with forward | reverse
    · rw [(ownU C).2,cs] at forward
      exact Or.inl forward
    · have own := (strict_bounds C _ _ C.c C.s C.unit_normal center).1
      have other := (strict_bounds A _ _ C.c C.s C.unit_normal east).2
      exfalso
      nlinarith only [reverse,own,other,dp]
  · have unit : (-C.s)^2+C.c^2=1 := by nlinarith only [C.unit_normal]
    rcases sep _ _ _ (transverse_radius C A) cv with forward | reverse
    · have own := (strict_bounds C _ _ (-C.s) C.c unit center).2
      have other := (strict_bounds A _ _ (-C.s) C.c unit east).1
      rw [cs] at own other forward
      exfalso
      nlinarith only [forward,own,other,cn.1]
    · have own := (strict_bounds C _ _ (-C.s) C.c unit center).1
      have other := (strict_bounds A _ _ (-C.s) C.c unit north).2
      exfalso
      nlinarith only [reverse,own,other,dp]
  · have identity : supportRadius C A.c A.s+supportRadius A A.c A.s=pairRadius A C := by
      rw [add_comm]
      exact parallel_radius A C
    rcases sep _ _ _ identity au with forward | reverse
    · right
      simpa only [(ownU A).1] using forward
    · have own := (strict_bounds C _ _ A.c A.s A.unit_normal center).1
      have other := (strict_bounds A _ _ A.c A.s A.unit_normal east).2
      exfalso
      nlinarith only [reverse,own,other,ac]
  · have identity : supportRadius C (-A.s) A.c+supportRadius A (-A.s) A.c=pairRadius A C := by
      rw [add_comm]
      exact transverse_radius A C
    have unit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    rcases sep _ _ _ identity av with forward | reverse
    · have own := (strict_bounds C _ _ (-A.s) A.c unit center).2
      have other := (strict_bounds A _ _ (-A.s) A.c unit east).1
      exfalso
      nlinarith only [forward,own,other,asign]
    · have own := (strict_bounds C _ _ (-A.s) A.c unit center).1
      have other := (strict_bounds A _ _ (-A.s) A.c unit north).2
      exfalso
      nlinarith only [reverse,own,other,ac]

private theorem lower_offset (A : OpenSquare) (d r : ℝ)
    (ac : 0 < A.c) (asign : 0 ≤ A.s) (dp : 0 < d) (rn : 0 ≤ r)
    (unit : d^2+r^2=1) (offset : 0 ≤ A.loU)
    (north : A.Inside 0 (13/50)) (east : A.Inside (13/50) 0) :
    lower A d r ≤ A.loU := by
  let alpha := A.c*d+A.s*r
  let beta := A.s*d-A.c*r
  have ap : 0 < alpha := by
    dsimp [alpha]
    nlinarith only [mul_pos ac dp,mul_nonneg asign rn]
  have identity : alpha^2+beta^2=1 := by
    calc
      _ = (A.c^2+A.s^2)*(d^2+r^2) := by dsimp [alpha,beta]; ring
      _ = 1 := by rw [A.unit_normal,unit]; norm_num
  have upperAlpha : alpha ≤ 1 := by nlinarith only [identity,sq_nonneg beta,sq_nonneg (alpha-1)]
  have first : alpha*A.loU ≤ A.loU := by
    calc
      _ ≤ 1*A.loU := mul_le_mul_of_nonneg_right upperAlpha offset
      _ = A.loU := one_mul _
  have formula := lower_in_bands A d r
  have u : d*A.c+r*A.s=alpha := by dsimp [alpha]; ring
  have v : -d*A.s+r*A.c=-beta := by dsimp [beta]; ring
  rw [u,v,abs_of_pos ap] at formula
  by_cases sign : 0 ≤ beta
  · rw [abs_of_nonpos (neg_nonpos.mpr sign)] at formula
    have face : 0 ≤ A.loV+A.side := by linarith only [north.2.2.2,ac]
    have last := mul_nonneg sign face
    calc
      lower A d r = alpha*A.loU-beta*(A.loV+A.side) := by rw [formula]; ring
      _ ≤ alpha*A.loU := sub_le_self _ last
      _ ≤ A.loU := first
  · have negative : beta ≤ 0 := le_of_lt (lt_of_not_ge sign)
    rw [abs_of_nonneg (neg_nonneg.mpr negative)] at formula
    have face : A.loV ≤ 0 := by linarith only [east.2.2.1,asign]
    have last := mul_nonneg_of_nonpos_of_nonpos negative face
    calc
      lower A d r = alpha*A.loU-beta*A.loV := by rw [formula]; ring
      _ ≤ alpha*A.loU := sub_le_self _ last
      _ ≤ A.loU := first

private theorem left_support (C : OpenSquare) (r : ℝ) (cs : C.s=r)
    (center : C.Inside 0 0) (avoid : ∀ y : ℝ, ¬ C.Inside (-1) y) :
    -1 ≤ C.c*C.loU-r*(C.loV+C.side) := by
  have bound (x y : ℝ) (point : C.Inside x y) : -1 ≤ x := by
    apply le_of_not_gt
    intro lower
    let t := (-1-x)/(-x)
    have denominator : 0 < -x := by linarith only [lower]
    have positive : 0 < t := div_pos (by linarith only [lower]) denominator
    have small : t < 1 := (div_lt_one denominator).mpr (by linarith)
    have relation : t*(-x)=-1-x := div_mul_cancel₀ _ denominator.ne'
    have point' := inside_segment C x y 0 0 t point center positive.le small.le
    have identity : (1-t)*x+t*0=-1 := by nlinarith only [relation]
    rw [identity] at point'
    exact avoid _ point'
  have limit : 0 ≤ C.c*C.loU-r*(C.loV+C.side)+1 := by
    apply affine_endpoint_nonnegative C.side (C.c+r) _ C.side_pos
    intro t positive small
    let u := C.loU+t
    let v := C.loV+C.side-t
    have point : C.Inside (C.c*u-C.s*v) (C.s*u+C.c*v) := by
      apply (inside_iff_rotated_box C _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have h := bound _ _ point
    rw [cs] at h
    dsimp [u,v] at h
    nlinarith only [h]
  linarith only [limit]

private theorem bottom_support (C : OpenSquare) (r : ℝ) (cs : C.s=r)
    (center : C.Inside 0 0) (avoid : ∀ x : ℝ, ¬ C.Inside x (-1)) :
    -1 ≤ r*C.loU+C.c*C.loV := by
  have bound (x y : ℝ) (point : C.Inside x y) : -1 ≤ y := by
    apply le_of_not_gt
    intro lower
    let t := (-1-y)/(-y)
    have denominator : 0 < -y := by linarith only [lower]
    have positive : 0 < t := div_pos (by linarith only [lower]) denominator
    have small : t < 1 := (div_lt_one denominator).mpr (by linarith)
    have relation : t*(-y)=-1-y := div_mul_cancel₀ _ denominator.ne'
    have point' := inside_segment C x y 0 0 t point center positive.le small.le
    have identity : (1-t)*y+t*0=-1 := by nlinarith only [relation]
    rw [identity] at point'
    exact avoid _ point'
  have limit : 0 ≤ r*C.loU+C.c*C.loV+1 := by
    apply affine_endpoint_nonnegative C.side (C.c+r) _ C.side_pos
    intro t positive small
    let u := C.loU+t
    let v := C.loV+t
    have point : C.Inside (C.c*u-C.s*v) (C.s*u+C.c*v) := by
      apply (inside_iff_rotated_box C _ _).mpr
      refine ⟨u,v,?_,rfl,rfl⟩
      dsimp [u,v,InBands]
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [positive,small]
    have h := bound _ _ point
    rw [cs] at h
    dsimp [u,v] at h
    nlinarith only [h]
  linarith only [limit]

theorem bound (C A : OpenSquare) (r : ℝ) (cs : C.s=r) (cn : Normal C.c r)
    (side : 1 < C.side) (cap : C.side ≤ 1001/1000) (same : C.side=A.side)
    (ac : 0 < A.c) (asign : 0 ≤ A.s)
    (center : C.Inside 0 0) (west : C.Inside (-(1/2)) 0) (bottom : C.Inside 0 (-(1/2)))
    (marker : C.Inside (-(7/20)) (-(7/20)))
    (missingNW : ¬ C.Inside (-(7/20)) (7/20))
    (missingSE : ¬ C.Inside (7/20) (-(7/20)))
    (bottomSegment : ∀ x : ℝ, -(4/5) ≤ x → x ≤ -(13/50) → ¬ C.Inside x (-1))
    (leftSegment : ∀ y : ℝ, -(14/25) ≤ y → y ≤ 0 → ¬ C.Inside (-1) y)
    (north : A.Inside 0 (13/50)) (east : A.Inside (13/50) 0)
    (aMarker : A.Inside (7/20) (7/20))
    (aMissingO : ¬ A.Inside 0 0) (aMissingF : ¬ A.Inside (13/50) 1)
    (aSegment : ∀ y : ℝ, 13/50 ≤ y → y ≤ 4/5 → ¬ A.Inside 1 y)
    (apart : ∀ x y, ¬ (C.Inside x y ∧ A.Inside x y)) : r < 8/25 := by
  have cb := normal_bounds cn
  have dp : 0 < C.c := by linarith only [cb.1]
  have sideA : 1 < A.side := by rwa [←same]
  have offset := C981CompletionOppositeOffset.bounds A sideA ac asign north east aMarker aMissingO aMissingF aSegment
  have modes := positive_axes C A r cs cn ac asign same center north east apart
  have lowerA := lower_offset A C.c r ac asign dp cn.1 cn.2.2 offset.2.1 north east
  have uCap : C.loU+C.side ≤ (7/20)*(C.c-r) := by
    have vCap : C.loV+C.side ≤ (7/20)*(C.c+r) := by
      apply le_of_not_gt
      intro high
      apply missingNW
      refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
        linarith only [marker.1,center.2.1,center.2.2.1,cn.1,cn.2.1,dp,high,cs]
    have short := (short_projections C (7/10) (7/10) (by norm_num)).2.1
    rw [cs] at short
    apply le_of_not_gt
    intro high
    apply missingSE
    refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
      linarith only [center.1,center.2.2.2,cn.1,cn.2.1,dp,high,vCap,short,side,cs]
  have vCap : C.loV+C.side ≤ (7/20)*(C.c+r) := by
    apply le_of_not_gt
    intro high
    apply missingNW
    refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;>
      linarith only [marker.1,center.2.1,center.2.2.1,cn.1,cn.2.1,dp,high,cs]
  apply lt_of_not_ge
  intro large
  have rp : 0 < r := by linarith only [large]
  have centerU : 0 < C.loU+C.side := by simpa [OpenSquare.Inside,InBands] using center.2.1
  have kHighU : -(13/50)*C.c-r < C.loU+C.side := by linarith only [centerU,dp,cn.1]
  have kHighV : (13/50)*r-C.c < C.loV+C.side := by
    have own := center.2.2.2
    rw [cs] at own
    linarith only [own,dp,cn.2.1]
  have short := (short_projections C (61/100) (13/20) (by norm_num)).2.1
  rw [cs] at short
  have kLowU : C.loU < -(13/50)*C.c-r := by linarith only [uCap,short,side]
  have kFace : (13/50)*r-C.c ≤ C.loV := by
    apply le_of_not_gt
    intro low
    apply bottomSegment (-(13/50)) (by norm_num) le_rfl
    refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;> linarith only [kLowU,kHighU,low,kHighV]
  have jHighU : -(4/5)*C.c-r < C.loU+C.side := by linarith only [centerU,dp,cn.1]
  have jHighV : (4/5)*r-C.c < C.loV+C.side := by
    have own := center.2.2.2
    rw [cs] at own
    linarith only [own,dp,cn.2.1]
  have jModes : -(4/5)*C.c-r ≤ C.loU ∨ (4/5)*r-C.c ≤ C.loV := by
    by_cases u : -(4/5)*C.c-r ≤ C.loU
    · exact Or.inl u
    · right
      apply le_of_not_gt
      intro low
      apply bottomSegment (-(4/5)) le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;> linarith only [u,jHighU,low,jHighV]
  have bottomWall : -1 ≤ r*C.loU+C.c*C.loV := by
    rcases jModes with ju | jv
    · have noLine : ∀ x : ℝ, ¬ C.Inside x (-1) := by
        intro x point
        have low : -(4/5) < x := by
          have own := point.1
          rw [cs] at own
          have product : 0 < C.c*(x+4/5) := by linarith only [own,ju]
          exact sub_pos.mp (pos_of_mul_pos_right (by convert product using 1 <;> ring) dp.le)
        have high : x < -(13/50) := by
          have own := point.2.2.1
          rw [cs] at own
          have product : 0 < r*(-(13/50)-x) := by linarith only [own,kFace]
          exact sub_pos.mp (pos_of_mul_pos_right product cn.1)
        exact bottomSegment x low.le high.le point
      exact bottom_support C r cs center noLine
    · have outward : C.side < r+(4/5)*C.c := by
        by_cases high : 9/20 ≤ r
        · linarith only [high,cb.1,cap]
        · have rLow : r ≤ 9/20 := le_of_lt (lt_of_not_ge high)
          have dLow : 89/100 ≤ C.c := by
            have sine := mul_nonneg (sub_nonneg.mpr rLow)
              (show 0 ≤ 9/20+r by linarith only [cn.1])
            apply le_of_not_gt
            intro low
            have cosine := mul_pos (show 0 < 89/100-C.c by linarith only [low])
              (show 0 < 89/100+C.c by linarith only [dp])
            nlinarith only [sine,cosine,cn.2.2]
          linarith only [large,dLow,cap]
      have one := mul_pos rp centerU
      have two := mul_nonneg dp.le (sub_nonneg.mpr jv)
      have three := mul_pos rp (sub_pos.mpr outward)
      nlinarith only [one,two,three,cn.2.2]
  have jlHighU : -C.c-(14/25)*r < C.loU+C.side := by linarith only [centerU,dp,cn.1]
  have jlHighV : r-(14/25)*C.c < C.loV+C.side := by
    have own := west.2.2.2
    rw [cs] at own
    linarith only [own,dp,cn.2.1]
  have jlLowV : C.loV < r-(14/25)*C.c := by linarith only [vCap,side,cb.2.1,cn.1]
  have jlFace : -C.c-(14/25)*r ≤ C.loU := by
    apply le_of_not_gt
    intro low
    apply leftSegment (-(14/25)) le_rfl (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;> linarith only [low,jlHighU,jlLowV,jlHighV]
  have klHighU : -C.c < C.loU+C.side := by linarith only [centerU,dp]
  have klLowV : C.loV < r := by
    have own := west.2.2.1
    rw [cs] at own
    linarith only [own,cn.1]
  have leftWall : -1 ≤ C.c*C.loU-r*(C.loV+C.side) := by
    have floorImpossible (floor : -C.c ≤ C.loU) : False := by
      have defect := (C981CompletionOppositeSupport.large_bounds cn large).2.2
      have uLarge : 32/625 < C.loU+C.side := by linarith only [floor,side,defect]
      rcases modes with own | other
      · linarith only [own,lowerA,offset.2.2,uLarge]
      · have support := C981CompletionOppositeSupport.floor_upper C r A.c A.s cs cn side cap
          large ac asign A.unit_normal floor west bottom
        linarith only [other,support,offset.2.2,side,defect]
    have klLowU : C.loU < -C.c := lt_of_not_ge floorImpossible
    have klFace : C.loV+C.side ≤ r := by
      apply le_of_not_gt
      intro high
      apply leftSegment 0 (by norm_num) le_rfl
      refine ⟨?_,?_,?_,?_⟩ <;> rw [cs] <;> linarith only [klLowU,klHighU,klLowV,high]
    have noLine : ∀ y : ℝ, ¬ C.Inside (-1) y := by
      intro y point
      have low : -(14/25) < y := by
        have own := point.1
        rw [cs] at own
        have product : 0 < r*(y+14/25) := by linarith only [own,jlFace]
        exact sub_pos.mp (pos_of_mul_pos_right (by convert product using 1 <;> ring) cn.1)
      have high : y < 0 := by
        have own := point.2.2.2
        rw [cs] at own
        have product : 0 < C.c*(-y) := by linarith only [own,klFace]
        have negative := pos_of_mul_pos_right product dp.le
        linarith only [negative]
      exact leftSegment y low.le high.le point
    exact left_support C r cs center noLine
  rcases modes with own | other
  · have support := C981CompletionOppositeSupport.wall_upper C r C.c r cs cn side cap
      large dp cn.1 cn.2.2 leftWall bottomWall
    have formula := (ownU C).2
    rw [cs] at formula
    rw [formula] at support
    linarith only [own,lowerA,support,offset.2.2]
  · have support := C981CompletionOppositeSupport.wall_upper C r A.c A.s cs cn side cap
      large ac asign A.unit_normal leftWall bottomWall
    linarith only [other,support,offset.2.2]

#print axioms bound
end N12Compact.C981CompletionOppositeAngle
