import Compact.Geometry.CentralWallPairSupport
import S12.ShortCluster

/-! The actual half-angle crossing is impossible with the short endpoint
1197/500. Every full-square separating axis and both orders are included.
The existing exact longitudinal margins are reused without changing their
mathematical premises. This remains a local lemma, not a BranchEnding. -/
namespace N12Compact.C1092ShortWallCrossing
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open CentralWallEscape CentralWallPairAxes CentralWallPairSupport
set_option Elab.async false

private theorem lower_face (R : OpenSquare) (hc : 0 < R.c) (hs : 0 ≤ R.s)
    (z : ℝ) (hz : 0 ≤ z) (zhi : z < 197/500)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (1197/500))
    (missing : ¬ R.Inside 3 (2+z)) : R.c*3+R.s*(2+z) ≤ R.loU := by
  have uhi : R.c*3+R.s*(2+z) < R.loU+R.side := by
    nlinarith only [high.2.1,mul_nonneg hs (sub_nonneg.mpr zhi.le)]
  have vlo : R.loV < -R.s*3+R.c*(2+z) := by
    nlinarith only [marker.2.2.1,mul_nonneg hc.le hz,hs]
  have vhi : -R.s*3+R.c*(2+z) < R.loV+R.side := by
    nlinarith only [high.2.2.2,mul_pos hc (sub_pos.mpr zhi)]
  exact le_of_not_gt (fun h => missing ⟨h,uhi,vlo,vhi⟩)

theorem outer_point (A : OpenSquare) (ha : 1 < A.side)
    (cn : C977CornerCubic.Normal A.c A.s)
    (q : A.Inside (113/50) 2) (m : A.Inside (47/20) (47/20))
    (gv : -(47/20)*A.s+(33/20)*A.c ≤ A.loV)
    (top : A.loV+A.side ≤ 3*A.c-(1197/500)*A.s)
    (missingB : ¬ A.Inside (33/20) (47/20)) :
    A.Inside (47/20) (53/20) := by
  have cb := C977CornerCubic.normal_bounds cn
  have cp : 0 < A.c := by linarith only [cb.1]
  have sum : (7/10)*(A.c+A.s) ≤ 1 := by linarith only [cb.2.2.2.2.2]
  have bu1 : A.c*(33/20)+A.s*(47/20) < A.loU+A.side := by
    linarith only [m.2.1,cp]
  have bv0 : A.loV < -A.s*(33/20)+A.c*(47/20) := by
    linarith only [q.2.2.1,cp,cn.1]
  have bv1 : -A.s*(33/20)+A.c*(47/20) < A.loV+A.side := by
    linarith only [gv,ha,sum]
  have bu0 : A.c*(33/20)+A.s*(47/20) ≤ A.loU :=
    le_of_not_gt (fun h => missingB ⟨h,bu1,bv0,bv1⟩)
  have shortU := short_projections A (47/20-33/20) (53/20-47/20) (by norm_num)
  have shortV := short_projections A (1197/500-47/20) (3-53/20) (by norm_num)
  exact ⟨by linarith only [m.1,cn.1],
    by linarith only [bu0,ha,shortU.2.1],
    by linarith only [top,ha,shortV.2.2.2],
    by linarith only [gv,ha,cb.2.1]⟩

private theorem alternatives (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side)
    (ac : 0 < A.c) (aNonneg : 0 ≤ A.s) (narrow : 12*A.s ≤ 5*A.c)
    (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (aq : A.Inside (113/50) 2)
    (gv : -(47/20)*A.s+(33/20)*A.c ≤ A.loV)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (1197/500))
    (z : ℝ) (hz : 0 ≤ z) (zhi : z < 197/500)
    (crossing : A.Inside 3 (2+z))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side ≤ lower R A.c A.s ∨ upper A R.c R.s ≤ R.loU := by
  have acu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,ac]
  have highVlo : A.loV < -A.s*3+A.c*(1197/500) := by
    linarith only [aq.2.2.1,narrow,ac]
  have highVhi : -A.s*3+A.c*(1197/500) < A.loV+A.side := by
    linarith only [gv,acu,aNonneg,ha]
  have crossVlo : R.loV < -R.s*3+R.c*(2+z) := by
    nlinarith only [marker.2.2.1,mul_nonneg rc.le hz,rs]
  have crossVhi : -R.s*3+R.c*(2+z) < R.loV+R.side := by
    nlinarith only [high.2.2.2,mul_pos rc (sub_pos.mpr zhi)]
  have axes := CongruentSAT.faceSeparation_of_disjoint A R same apart
  change pairRadius A R ≤ |A.c*(centerX R-centerX A)+A.s*(centerY R-centerY A)| ∨
    pairRadius A R ≤ |-A.s*(centerX R-centerX A)+A.c*(centerY R-centerY A)| ∨
    pairRadius R A ≤ |R.c*(centerX R-centerX A)+R.s*(centerY R-centerY A)| ∨
    pairRadius R A ≤ |-R.s*(centerX R-centerX A)+R.c*(centerY R-centerY A)| at axes
  have split (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius R nx ny=radius)
      (sep : radius ≤ |nx*(centerX R-centerX A)+ny*(centerY R-centerY A)|) :=
    separated A R nx ny (by rwa [identity])
  rcases axes with au | av | ru | rv
  · have sep := split A.c A.s _ (parallel_radius A R) au
    rw [(ownU A).1,(ownU A).2] at sep
    rcases sep with forward | reverse
    · exact Or.inl forward
    · have bound := (strict_bounds R _ _ A.c A.s A.unit_normal marker).2
      exfalso
      linarith only [reverse,bound,aq.1,ac]
  · have sep := split (-A.s) A.c _ (transverse_radius A R) av
    rw [(ownV A).1,(ownV A).2] at sep
    have bounds := strict_bounds R _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) high
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,bounds.1,bounds.2,highVlo,highVhi]
  · have identity : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]
      exact parallel_radius R A
    have sep := split R.c R.s _ identity ru
    rw [(ownU R).1,(ownU R).2] at sep
    rcases sep with forward | reverse
    · exact Or.inr forward
    · have bound := (strict_bounds A _ _ R.c R.s R.unit_normal aq).1
      exfalso
      linarith only [reverse,bound,marker.2.1,rc]
  · have identity : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]
      exact transverse_radius R A
    have sep := split (-R.s) R.c _ identity rv
    rw [(ownV R).1,(ownV R).2] at sep
    have bounds := strict_bounds A _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) crossing
    rcases sep with sep | sep <;> exfalso <;>
      linarith only [sep,bounds.1,bounds.2,crossVlo,crossVhi]

theorem central_axis_impossible (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (ac : 0 < A.c) (aNonneg : 0 ≤ A.s) (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (narrow : 12*A.s ≤ 5*A.c) (cross : 0 ≤ A.c*R.s-A.s*R.c)
    (lower : 2*A.c+2*A.s ≤ A.loU)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (1197/500))
    (axis : A.loU+A.side ≤ ABTransverse.lower R A.c A.s) : False := by
  classical
  let d := A.c*R.c+A.s*R.s
  let k := A.c*R.s-A.s*R.c
  have dp : 0 < d := add_pos_of_pos_of_nonneg (mul_pos ac rc) (mul_nonneg aNonneg rs)
  have kn : 0 ≤ k := cross
  have formula := (support_formulas A R dp.le cross).2
  change ABTransverse.lower R A.c A.s=d*R.loU-k*(R.loV+R.side) at formula
  have shallow : R.s < R.c := by
    by_contra notShallow
    have steep : R.c ≤ R.s := le_of_not_gt notShallow
    have highU := mul_lt_mul_of_pos_left marker.1 dp
    have highV := mul_le_mul_of_nonneg_left high.2.2.2.le kn
    have compose : d*(R.c*(1543/500)+R.s*2)-
        k*(-R.s*3+R.c*(1197/500)) =
        (1543/500)*A.c+2*A.s-k*((197/500)*R.c+(43/500)*R.s) := by
      dsimp [d,k]
      linear_combination ((1543/500)*A.c+2*A.s)*R.unit_normal
    have first := mul_nonneg (sub_nonneg.mpr steep)
      (show 0 ≤ (197/500)*A.c-(43/500)*A.s by linarith only [narrow,ac])
    have second := mul_nonneg rc.le
      (show 0 ≤ (77/250)*A.c-(12/25)*A.s by linarith only [narrow,ac])
    have gain : (43/500)*A.c ≤ k*((197/500)*R.c+(43/500)*R.s) := by
      have weighted := mul_nonneg rc.le (add_nonneg first second)
      have identity : k*((197/500)*R.c+(43/500)*R.s)-(43/500)*A.c =
          R.c*((R.s-R.c)*((197/500)*A.c-(43/500)*A.s)+
            R.c*((77/250)*A.c-(12/25)*A.s)) := by
        dsimp [k]
        linear_combination (43/500)*A.c*R.unit_normal
      nlinarith only [weighted,identity]
    have acu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,ac]
    have strictSupport : ABTransverse.lower R A.c A.s <
        (1543/500)*A.c+2*A.s-k*((197/500)*R.c+(43/500)*R.s) := by
      rw [formula,←compose]
      exact (sub_lt_sub_right highU _).trans_le (sub_le_sub_left highV _)
    have supportCap : (1543/500)*A.c+2*A.s-k*((197/500)*R.c+(43/500)*R.s) ≤
        3*A.c+2*A.s := by
      convert sub_le_sub_left gain ((1543/500)*A.c+2*A.s) using 1 <;> ring
    have needed : 2*A.c+2*A.s+A.side < 3*A.c+2*A.s :=
      ((add_le_add_left lower A.side).trans axis).trans_lt
        (strictSupport.trans_le supportCap)
    linarith only [needed,ha,acu]
  have wall := mul_le_mul_of_nonneg_left (CentralWallEscape.right_wall R box) dp.le
  have markerBound := mul_le_mul_of_nonneg_left marker.2.2.1.le aNonneg
  have cancellation : d*R.s-R.c*k=A.s := by
    dsimp [d,k]
    linear_combination A.s*R.unit_normal
  have supportBound : R.c*ABTransverse.lower R A.c A.s ≤
      R.c*(4*A.c+2*A.s)+(457/500)*A.s*R.s-R.side*R.c*(d+k) := by
    have expanded : R.c*ABTransverse.lower R A.c A.s =
        d*(R.c*(R.loU+R.side)-R.s*R.loV)+A.s*R.loV-
          R.side*R.c*(d+k) := by
      rw [formula]
      nlinarith only [congrArg (fun x : ℝ => x*R.loV) cancellation]
    calc
      R.c*ABTransverse.lower R A.c A.s =
          d*(R.c*(R.loU+R.side)-R.s*R.loV)+A.s*R.loV-
            R.side*R.c*(d+k) := expanded
      _ ≤ d*4+A.s*(-R.s*(1543/500)+R.c*2)-R.side*R.c*(d+k) :=
        sub_le_sub_right (add_le_add wall markerBound) _
      _ = _ := by dsimp [d]; ring
  have scaledAxis := mul_le_mul_of_nonneg_left axis rc.le
  have scaledLower := mul_le_mul_of_nonneg_left lower rc.le
  have original := CentralWallParallelMargin.parallel_margin
    (show C977CornerCubic.Normal A.c A.s from
      ⟨aNonneg,by linarith only [narrow,ac],A.unit_normal⟩)
    (show C977CornerCubic.Normal R.c R.s from ⟨rs,shallow.le,R.unit_normal⟩)
    narrow cross
  have ratio : R.c*(R.s/R.c)=R.s := by field_simp [ne_of_gt rc]
  have scaledMargin := mul_nonneg rc.le original
  have strict := mul_pos (sub_pos.mpr ha)
    (mul_pos rc (show 0 < 1+d+k by linarith only [dp,kn]))
  rw [← same] at supportBound
  have scaledMargin' : 0 ≤ R.c*(1+d+k-2*A.c-(457/500)*A.s*(R.s/R.c)) := by
    dsimp [d,k]
    nlinarith only [scaledMargin]
  have ratioScaled := congrArg (fun x : ℝ => (457/500)*A.s*x) ratio
  have scaleIdentity : R.c*((457/500)*A.s*(R.s/R.c)) =
      (457/500)*A.s*R.s := by
    calc
      _ = (457/500)*A.s*(R.c*(R.s/R.c)) := by ring
      _ = _ := ratioScaled
  rw [mul_sub,scaleIdentity] at scaledMargin'
  have combined : R.c*(2*A.c+2*A.s+A.side) ≤
      R.c*(4*A.c+2*A.s)+(457/500)*A.s*R.s-A.side*R.c*(d+k) := by
    calc
      _ = R.c*(2*A.c+2*A.s)+R.c*A.side := by ring
      _ ≤ R.c*A.loU+R.c*A.side := add_le_add_left scaledLower _
      _ = R.c*(A.loU+A.side) := by ring
      _ ≤ _ := scaledAxis.trans supportBound
  have nonpositive : (A.side-1)*(R.c*(1+d+k)) ≤ 0 := by
    calc
      _ = (R.c*(2*A.c+2*A.s+A.side)-
          (R.c*(4*A.c+2*A.s)+(457/500)*A.s*R.s-A.side*R.c*(d+k)))-
          (R.c*(1+d+k-2*A.c)-(457/500)*A.s*R.s) := by ring
      _ ≤ 0 := sub_nonpos.mpr ((sub_nonpos.mpr combined).trans scaledMargin')
  exact (not_le_of_gt strict) nonpositive

/-- An actual strict crossing between the two short walls is impossible.
Both physical wall-square orientation quadrants are retained by reindexing. -/
theorem impossible (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side) (box : InsideContainer R)
    (cn : C977CornerCubic.Normal A.c A.s)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬ A.Inside (47/20) (33/20))
    (missingB : ¬ A.Inside (33/20) (47/20))
    (missing : ¬ A.Inside 2 2)
    (top : A.loV+A.side ≤ 3*A.c-(1197/500)*A.s)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (1197/500))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y))
    (z : ℝ) (hz : 0 ≤ z) (zhi : z < 197/500)
    (angle : (1+A.c)*z=A.s) (unitAngle : A.s*z=1-A.c)
    (crossing : A.Inside 3 (2+z)) : False := by
  have cb := C977CornerCubic.normal_bounds cn
  have cp : 0 < A.c := by linarith only [cb.1]
  obtain ⟨W,wc,ws,side,inside,_⟩ := ClosedFrames.positive_frame R
  have sameW : A.side=W.side := same.trans side.symm
  have wb : InsideContainer W := fun x y h => box x y ((inside x y).mp h)
  have wm := (inside _ _).mpr marker
  have wh := (inside _ _).mpr high
  have disjoint : ∀ x y, ¬ (A.Inside x y ∧ W.Inside x y) :=
    fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
  have face := lower_face W wc ws z hz zhi wm wh
    (fun h => disjoint _ _ ⟨crossing,h⟩)
  have walls := wall_inequalities W (by simpa only [←sameW] using ha) wc ws wb z wm face
  have small := half_angle_lt W.c W.s z wc ws W.unit_normal hz walls.1 walls.2
  have narrow := slope_of_half_angle A.c A.s z cp hz angle unitAngle small
  have lower := central_lower_faces A cp cn.1 narrow.le p q m missing missingG
  have outer := outer_point A ha cn q m lower.2 top missingB
  have turn := wall_angle_order A.c A.s W.c W.s z
    (cosine_bound A.c A.s cp cn.1 A.unit_normal narrow.le) cn.1 wc ws
    A.unit_normal W.unit_normal hz angle walls.2
  have cross : 0 ≤ A.c*W.s-A.s*W.c := sub_nonneg.mpr turn.le
  rcases alternatives A W ha sameW cp cn.1 narrow.le wc ws q lower.2 wm wh
      z hz zhi crossing disjoint with axis | axis
  · exact central_axis_impossible A W ha sameW wb cp cn.1 wc ws narrow.le cross
      lower.1 wm wh axis
  · exact CentralWallPairSupport.wall_axis_impossible A W ha sameW wb cp cn.1 wc ws
      narrow.le cross lower.1 lower.2 outer wm axis

#print axioms impossible
end N12Compact.C1092ShortWallCrossing
