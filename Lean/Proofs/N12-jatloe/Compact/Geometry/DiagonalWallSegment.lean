import Compact.Geometry.CentralWallCenter
import Compact.Geometry.C977CornerCubic

/-! An actual neighboring square owns both ends of the diagonal segment
from (3,2.4) to (2.4,3). This segment excludes two outer points of an
elbow square, and directly intersects every middle-angle center escape. -/
namespace N12Compact.DiagonalWallSegment
open S12 S12Pilot FourSquareAnchors
set_option Elab.async false

theorem missing_top (A R : OpenSquare)
    (q : A.Inside (113/50) 2)
    (right : R.Inside 3 (12/5)) (top : R.Inside (12/5) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    ¬A.Inside (5/2) 3 := by
  intro high
  have a := inside_segment A (5/2) 3 (113/50) 2 (5/62)
    high q (by norm_num) (by norm_num)
  have r := inside_segment R (12/5) 3 3 (12/5) (25/186)
    top right (by norm_num) (by norm_num)
  apply apart (769/310) (181/62)
  constructor <;> norm_num at a r ⊢
  · exact a
  · exact r

theorem missing_right (A R : OpenSquare)
    (p : A.Inside 2 (113/50))
    (right : R.Inside 3 (12/5)) (top : R.Inside (12/5) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    ¬A.Inside 3 (5/2) := by
  intro high
  have a := inside_segment A 3 (5/2) 2 (113/50) (5/62)
    high p (by norm_num) (by norm_num)
  have r := inside_segment R 3 (12/5) (12/5) 3 (25/186)
    right top (by norm_num) (by norm_num)
  apply apart (181/62) (769/310)
  constructor <;> norm_num at a r ⊢
  · exact a
  · exact r

private theorem middle_margin {c s : ℝ} (hc : 0<c) (hs : 0≤s)
    (unit : c^2+s^2=1) (order : c≤s) (half : s≤2*c) :
    0<c+s-21/20-(7/10)*c*s := by
  have hsum : c+s≤10/7 := by
    nlinarith only [unit,sq_nonneg (c-s),sq_nonneg (c+s-10/7)]
  have product := mul_nonneg (sub_nonneg.mpr half)
    (show 0≤2*s-c by linarith only [hc,order])
  have lower : 4/3≤c+s := by
    apply le_of_not_gt
    intro wrong
    have square := mul_nonneg (sub_nonneg.mpr wrong.le)
      (show 0≤c+s+4/3 by linarith only [hc,hs])
    nlinarith only [product,square,unit]
  have chord := mul_nonneg (sub_nonneg.mpr lower)
    (show 0≤1-(7/20)*(c+s+4/3) by linarith only [hsum])
  nlinarith only [chord,unit]

/-- A single continuously chosen point of the genuine segment is
inside A. Its V coordinate equals that of A's strict central marker. -/
theorem middle_impossible (A R : OpenSquare) (ha : 1<A.side)
    (hc : 0<A.c) (hs : 0≤A.s) (order : A.c≤A.s) (half : A.s≤2*A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20)) (missing : ¬A.Inside 2 2)
    (right : R.Inside 3 (12/5)) (top : R.Inside (12/5) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) : False := by
  have centerUhi : 2*A.c+2*A.s<A.loU+A.side := by
    linarith only [m.2.1,hc,hs]
  have centerVlo : A.loV< -2*A.s+2*A.c := by
    linarith only [q.2.2.1,hs]
  have centerVhi : -2*A.s+2*A.c<A.loV+A.side := by
    linarith only [p.2.2.2,hc]
  have lowerU : 2*(A.c+A.s)≤A.loU := by
    apply le_of_not_gt
    intro wrong
    exact missing ⟨by linarith only [wrong],by linarith only [centerUhi],
      by linarith only [centerVlo],by linarith only [centerVhi]⟩
  let k := (13*A.s-A.c)/(12*(A.c+A.s))
  let x := 3-(3/5)*k
  let y := (12/5)+(3/5)*k
  have denominator : 0<12*(A.c+A.s) := by linarith only [hc,hs]
  have kp : 0≤k := div_nonneg (by linarith only [hc,order]) denominator.le
  have k1 : k≤1 := by
    apply (div_le_iff₀ denominator).mpr
    linarith only [hc,half]
  have multiply : 12*(A.c+A.s)*k=13*A.s-A.c := by
    dsimp [k]; field_simp [ne_of_gt denominator]
  have rInside : R.Inside x y := by
    have point := inside_segment R 3 (12/5) (12/5) 3 k right top kp k1
    convert point using 1 <;> dsimp [x,y] <;> ring
  have vIdentity : -A.s*x+A.c*y=-(47/20)*A.s+(47/20)*A.c := by
    dsimp [x,y]
    nlinarith only [multiply]
  have margin := middle_margin hc hs A.unit_normal order half
  have identity :
      (A.c+A.s)*(2*(A.c+A.s)+1-(A.c*x+A.s*y))=
        A.c+A.s-21/20-(7/10)*A.c*A.s := by
    dsimp [x,y]
    linear_combination (-(A.s-A.c)/20)*multiply-
      (21/20)*A.unit_normal
  have upper : A.c*x+A.s*y<2*(A.c+A.s)+1 := by
    have weighted : 0<(A.c+A.s)*(2*(A.c+A.s)+1-(A.c*x+A.s*y)) := by
      linarith only [identity,margin]
    have positive := pos_of_mul_pos_right weighted
      (show 0≤A.c+A.s by linarith only [hc,hs])
    linarith only [positive]
  have shift := mul_nonneg kp (sub_nonneg.mpr order)
  have first : A.loU<A.c*x+A.s*y := by
    dsimp [x,y]
    nlinarith only [m.1,hc,hs,shift]
  have aInside : A.Inside x y := by
    refine ⟨first,?_,?_,?_⟩
    · linarith only [upper,lowerU,ha]
    · rw [vIdentity]; linarith only [m.2.2.1]
    · rw [vIdentity]; linarith only [m.2.2.2]
  exact apart x y ⟨aInside,rInside⟩

#print axioms missing_top
#print axioms missing_right
#print axioms middle_impossible
end N12Compact.DiagonalWallSegment
