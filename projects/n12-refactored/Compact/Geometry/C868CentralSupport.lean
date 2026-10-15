import Compact.Geometry.ABTransverse
import Compact.Geometry.C977NegativeCorner
import Compact.Geometry.C868CentralMargins
import S12.ShortCluster

/-! The lower-left square's original missing auxiliary points constrain
its full support. The two point exclusions are retained separately: neither
one can be replaced by an unproved centre-point assertion. -/
namespace N12Compact.C868CentralSupport

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

/-- Three continuous face configurations for the actual lower-left square.
The second configuration has a necessary small-angle bound. -/
theorem modes (A : OpenSquare) (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (canonical : A.s ≤ A.c) (side : 1 < A.side)
    (southwest : A.Inside (33/20) (33/20))
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5)) :
    (8/5)*A.c+A.s ≤ A.loU ∨
      (8/5)*A.c-A.s ≤ A.loV ∧ 13*A.s < A.c ∨
      A.c+(8/5)*A.s ≤ A.loU ∧ A.c-(8/5)*A.s ≤ A.loV := by
  have upperBottomU : A.c*(8/5)+A.s*1 < A.loU+A.side := by
    nlinarith only [southwest.2.1,hc,hs]
  have upperBottomV : -A.s*(8/5)+A.c*1 < A.loV+A.side := by
    nlinarith only [southwest.2.2.2,hc,canonical]
  by_cases bottomU : A.c*(8/5)+A.s*1 ≤ A.loU
  · left
    nlinarith only [bottomU]
  · have bottomV : A.c-(8/5)*A.s ≤ A.loV := by
      apply le_of_not_gt
      intro lowerV
      apply missingBottom
      refine ⟨lt_of_not_ge bottomU,upperBottomU,?_,upperBottomV⟩
      nlinarith only [lowerV]
    have upperLeftU : A.c*1+A.s*(8/5) < A.loU+A.side := by
      nlinarith only [southwest.2.1,hc,hs]
    have span := (short_projections A (3/5) (3/5) (by norm_num)).2.1
    have upperLeftV : -A.s*1+A.c*(8/5) < A.loV+A.side := by
      nlinarith only [bottomV,span,side]
    by_cases leftU : A.c*1+A.s*(8/5) ≤ A.loU
    · right; right
      exact ⟨by nlinarith only [leftU],bottomV⟩
    · have leftV : (8/5)*A.c-A.s ≤ A.loV := by
        apply le_of_not_gt
        intro lowerV
        apply missingLeft
        refine ⟨lt_of_not_ge leftU,upperLeftU,?_,upperLeftV⟩
        nlinarith only [lowerV]
      right; left
      exact ⟨leftV,by nlinarith only [leftV,southwest.2.2.1]⟩

/-- The actual square extends past the northwest central marker in every
positive canonical support direction. This is a support statement, not a
claim that the northwest marker or the centre belongs to the square. -/
theorem positive_support (A : OpenSquare) (c s : ℝ)
    (hn : Normal c s) (hA : Normal A.c A.s) (side : 1 < A.side)
    (southwest : A.Inside (33/20) (33/20))
    (aD : A.Inside 2 (87/50)) (aQ : A.Inside (87/50) 2)
    (missingBottom : ¬ A.Inside (8/5) 1)
    (missingLeft : ¬ A.Inside 1 (8/5)) :
    (33/20)*c+(47/20)*s < upper A c s := by
  have bn := normal_bounds hn
  have ba := normal_bounds hA
  have cp : 0<c := by linarith only [bn.1]
  have ap : 0<A.c := by linarith only [ba.1]
  let α := c*A.c+s*A.s
  let β := s*A.c-c*A.s
  have betaIdentity : -c*A.s+s*A.c=β := by dsimp [β]; ring
  have alphaPos : 0<α := add_pos_of_pos_of_nonneg (mul_pos cp ap)
    (mul_nonneg hn.1 hA.1)
  have wide := mul_pos alphaPos (sub_pos.mpr side)
  have branches := modes A ap hA.1 hA.2.1 side southwest missingBottom missingLeft
  by_cases order : 0≤β
  · have formula : upper A c s=α*(A.loU+A.side)+β*(A.loV+A.side) := by
      rw [upper_in_bands,betaIdentity]
      change α*(A.loU+A.side/2)+β*(A.loV+A.side/2)+
        A.side/2*(|α|+|β|)=α*(A.loU+A.side)+β*(A.loV+A.side)
      rw [abs_of_nonneg alphaPos.le,abs_of_nonneg order]
      ring
    have extra := mul_nonneg order (sub_nonneg.mpr side.le)
    rcases branches with branch | ⟨branch,shallow⟩ | ⟨u,v⟩
    · have up := mul_nonneg alphaPos.le (sub_nonneg.mpr branch)
      have vp := mul_nonneg order (sub_nonneg.mpr aQ.2.2.2.le)
      have margin := C868CentralMargins.modeI_nonneg hn hA order
      change 0≤α*(1+(8/5)*A.c+A.s)+β*(2*A.c-(87/50)*A.s)-
        (33/20)*c-(47/20)*s at margin
      have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg wide up) vp) margin)
      apply lt_of_lt_of_eq (lt_add_of_pos_right ((33/20)*c+(47/20)*s) positive)
      rw [formula]
      ring
    · have up := mul_pos alphaPos (sub_pos.mpr aD.2.1)
      have vp := mul_nonneg order (sub_nonneg.mpr branch)
      have margin := C868CentralMargins.modeII_nonneg hn hA order shallow.le
      change 0≤α*(2*A.c+(87/50)*A.s)+β*(1+(8/5)*A.c-A.s)-
        (33/20)*c-(47/20)*s at margin
      have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg up vp) extra) margin)
      apply lt_of_lt_of_eq (lt_add_of_pos_right ((33/20)*c+(47/20)*s) positive)
      rw [formula]
      ring
    · have up := mul_nonneg alphaPos.le (sub_nonneg.mpr u)
      have vp := mul_nonneg order (sub_nonneg.mpr v)
      have margin := C868CentralMargins.modeIII_nonneg hn hA order
      change 0≤α*(1+A.c+(8/5)*A.s)+β*(1+A.c-(8/5)*A.s)-
        (33/20)*c-(47/20)*s at margin
      have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg wide up) vp) extra) margin)
      apply lt_of_lt_of_eq (lt_add_of_pos_right ((33/20)*c+(47/20)*s) positive)
      rw [formula]
      ring
  · have negative : β≤0 := le_of_not_ge order
    have formula : upper A c s=α*(A.loU+A.side)+β*A.loV := by
      rw [upper_in_bands,betaIdentity]
      change α*(A.loU+A.side/2)+β*(A.loV+A.side/2)+
        A.side/2*(|α|+|β|)=α*(A.loU+A.side)+β*A.loV
      rw [abs_of_nonneg alphaPos.le,abs_of_nonpos negative]
      ring
    have vp := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr aD.2.2.1.le)
    rcases branches with branch | ⟨branch,shallow⟩ | ⟨u,v⟩
    · have up := mul_nonneg alphaPos.le (sub_nonneg.mpr branch)
      have margin := C868CentralMargins.modeI_nonpos hn hA negative
      change 0≤α*(1+(8/5)*A.c+A.s)+β*((87/50)*A.c-2*A.s)-
        (33/20)*c-(47/20)*s at margin
      have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg wide up) vp) margin)
      apply lt_of_lt_of_eq (lt_add_of_pos_right ((33/20)*c+(47/20)*s) positive)
      rw [formula]
      ring
    · have scaled := mul_nonneg cp.le (sub_nonneg.mpr shallow.le)
      have bound : (13*s)*A.c≤c*A.c := by
        dsimp [β] at negative
        nlinarith only [negative,scaled]
      have shallowN : 13*s≤c := (mul_le_mul_right ap).mp bound
      have owned := strict_bounds A _ _ c s hn.2.2 aD
      nlinarith only [owned.2,shallowN,cp]
    · have up := mul_nonneg alphaPos.le (sub_nonneg.mpr u)
      have margin := C868CentralMargins.modeIII_nonpos hn hA negative
      change 0≤α*(1+A.c+(8/5)*A.s)+β*((87/50)*A.c-2*A.s)-
        (33/20)*c-(47/20)*s at margin
      have positive := (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg wide up) vp) margin)
      apply lt_of_lt_of_eq (lt_add_of_pos_right ((33/20)*c+(47/20)*s) positive)
      rw [formula]
      ring

end N12Compact.C868CentralSupport
