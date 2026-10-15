import Compact.Completion.C1092.ShortWallCrossing
import Compact.Completion.C1092.ShortWallScalars
import S12.Convex

/-! The entire central-angle entrance for the actual short-wall theorem.
A missing center forces a strict narrow angle and a genuine strict upper
point in the same square. No saved angle or center enclosure is assumed. -/
namespace N12Compact.C1092ShortWallNarrow
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

structure NarrowData (A : OpenSquare) : Prop where
  sine_pos : 0 < A.s
  narrow : 4*A.s < A.c
  escape : 2*(A.c+A.s) ≤ A.loU
  lowerV : -(47/20)*A.s+(33/20)*A.c ≤ A.loV
  topcap : A.loV+A.side ≤ 3*A.c-(1197/500)*A.s
  high : A.Inside (5/2) 3

/-- The strict point and every narrow-sector bound are derived from the
original two-wall entrance, with the exact endpoint 1197/500. -/
theorem of_missing (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (cn : Normal A.c A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (missingTop : ¬ A.Inside (1197/500) 3)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (1197/500))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (missing : ¬ A.Inside 2 2) : NarrowData A := by
  classical
  have cb := normal_bounds cn
  have cp : 0 < A.c := by linarith only [cb.1]
  have centerUhi : A.c*2+A.s*2 < A.loU+A.side := by
    linarith only [m.2.1,cp,cn.1]
  have centerVlo : A.loV < -A.s*2+A.c*2 := by
    linarith only [q.2.2.1,cn.1]
  have centerVhi : -A.s*2+A.c*2 < A.loV+A.side := by
    linarith only [p.2.2.2,cp]
  have escape : 2*(A.c+A.s) ≤ A.loU := by
    apply le_of_not_gt
    intro h
    exact missing ⟨by linarith only [h],centerUhi,centerVlo,centerVhi⟩
  have sp : 0 < A.s := by linarith only [escape,p.1]
  have sum : (7/10)*(A.c+A.s) ≤ 1 := by linarith only [cb.2.2.2.2.2]
  have topUlo : A.loU < A.c*(1197/500)+A.s*3 := by
    linarith only [m.1,cp,cn.1]
  have topUhi : A.c*(1197/500)+A.s*3 < A.loU+A.side := by
    linarith only [escape,ha,sum,cn.2.1,cp]
  have topVlo : A.loV < -A.s*(1197/500)+A.c*3 := by
    linarith only [q.2.2.1,cp,cn.2.1]
  have topcap : A.loV+A.side ≤ 3*A.c-(1197/500)*A.s := by
    apply le_of_not_gt
    intro h
    apply missingTop
    exact ⟨topUlo,topUhi,topVlo,by linarith only [h]⟩
  have sector : A.s < (16/25)*A.c := by
    apply lt_of_not_ge
    intro steep
    have steep' : 16*A.c/25 ≤ A.s := by linarith only [steep]
    have projectedSquare := C1092ShortWallScalars.steep_short_point cn steep'
    have projected : (1293/1250)*A.c+(591/2500)*A.s ≤ 1 := by
      nlinarith only [projectedSquare,sq_nonneg
        ((1293/1250)*A.c+(591/2500)*A.s-1)]
    have distance := short_projections A (1197/500-3793/1250)
      (3-5591/2500) (by norm_num)
    have inA : A.Inside (3793/1250) (5591/2500) :=
      ⟨by linarith only [m.1,cp,cn.2.1],
        by linarith only [escape,ha,projected],
        by linarith only [topcap,ha,distance.2.2.2],
        by linarith only [p.2.2.2,cp,cn.1]⟩
    have inR : R.Inside (3793/1250) (5591/2500) := by
      convert inside_segment R (1543/500) 2 3 (1197/500) (3/5)
        marker high (by norm_num) (by norm_num) using 1 <;> norm_num
    exact apart _ _ ⟨inA,inR⟩
  let z := A.s/(1+A.c)
  have denominator : 0 < 1+A.c := by linarith only [cp]
  have hz : 0 ≤ z := div_nonneg cn.1 denominator.le
  have angle : (1+A.c)*z=A.s := by dsimp [z]; field_simp [ne_of_gt denominator]
  have unitAngle : A.s*z=1-A.c := by
    dsimp [z]
    field_simp [ne_of_gt denominator]
    nlinarith only [A.unit_normal]
  have zhi : z < 197/500 := by
    apply (div_lt_iff₀ denominator).mpr
    linarith only [sector,cb.2.1]
  have narrow : 4*A.s < A.c := by
    apply lt_of_not_ge
    intro moderate
    have scalar := C1092ShortWallScalars.moderate_short_point cn moderate
    have margin := mul_nonneg hz (show 0 ≤ (197/500)*A.c+A.s-303/500 by
      linarith only [scalar])
    have cz : A.c*z ≤ A.s := by nlinarith only [angle,hz]
    have crossing : A.Inside 3 (2+z) :=
      ⟨by nlinarith only [q.1,cp,mul_nonneg cn.1 hz],
        by nlinarith only [escape,unitAngle,ha],
        by nlinarith only [topcap,unitAngle,angle,margin,ha],
        by nlinarith only [p.2.2.2,cz,cn.1,cp]⟩
    exact C1092ShortWallCrossing.impossible A R ha same box cn p q m missingG missingB
      missing topcap marker high apart z hz zhi angle unitAngle crossing
  have highA : A.Inside (5/2) 3 := by
    classical
    apply Classical.byContradiction
    intro absent
    have crossing := CentralWallEscape.crossing_point A ha cp cn.1 sector.le
      z hz angle unitAngle p q m absent missing
    exact C1092ShortWallCrossing.impossible A R ha same box cn p q m missingG missingB
      missing topcap marker high apart z hz zhi angle unitAngle crossing
  have lower := CentralWallPairAxes.central_lower_faces A cp cn.1
    (by linarith only [narrow,cp]) p q m missing missingG
  exact ⟨sp,narrow,escape,lower.2,topcap,highA⟩

#print axioms of_missing
end N12Compact.C1092ShortWallNarrow
