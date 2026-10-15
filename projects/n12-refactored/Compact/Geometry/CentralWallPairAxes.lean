import Compact.Geometry.CentralWallLongitudinal
import Compact.Geometry.ABTransverse

/-! Full-square separating-axis reduction for an escaping elbow and its
actual right wall. Both longitudinal alternatives are retained. -/
namespace N12Compact.CentralWallPairAxes
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
set_option Elab.async false

theorem central_lower_faces (A : OpenSquare) (hc : 0 < A.c) (hs : 0 ≤ A.s)
    (narrow : 12*A.s ≤ 5*A.c)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missing : ¬ A.Inside 2 2)
    (missingG : ¬ A.Inside (47/20) (33/20)) :
    2*A.c+2*A.s ≤ A.loU ∧
      -(47/20)*A.s+(33/20)*A.c ≤ A.loV := by
  constructor
  · apply le_of_not_gt
    intro lower
    exact missing ⟨by linarith only [lower],
      by linarith only [m.2.1,hc,hs],by linarith only [q.2.2.1,hs],
      by linarith only [p.2.2.2,hc]⟩
  · apply le_of_not_gt
    intro lower
    exact missingG ⟨by linarith only [p.1,narrow,hc],
      by linarith only [m.2.1,hs],by linarith only [lower],
      by linarith only [p.2.2.2,hc,hs]⟩

theorem cosine_bound (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s)
    (unit : c^2+s^2=1) (narrow : 12*s ≤ 5*c) : 12/13 ≤ c := by
  have product := mul_nonneg (sub_nonneg.mpr narrow)
    (show 0 ≤ 5*c+12*s by linarith only [hc,hs])
  by_contra small
  have square := mul_pos (sub_pos.mpr (lt_of_not_ge small))
    (show 0 < 12/13+c by linarith only [hc])
  nlinarith only [unit,product,square]

/-- The actual wall must turn farther than the central square. This
deduction uses the container wall, through its strict scalar consequence. -/
theorem wall_angle_order (c s r t z : ℝ)
    (hc : 12/13 ≤ c) (hs : 0 ≤ s) (hr : 0 < r) (ht : 0 ≤ t)
    (au : c^2+s^2=1) (ru : r^2+t^2=1)
    (hz : 0 ≤ z) (angle : (1+c)*z=s)
    (wall : r*t*z < 1-r-(43/500)*t^2) : s*r < c*t := by
  classical
  by_contra failure
  have order : c*t ≤ s*r := le_of_not_gt failure
  have squareOrder := mul_nonneg (sub_nonneg.mpr order)
    (show 0 ≤ s*r+c*t from add_nonneg (mul_nonneg hs hr.le)
      (mul_nonneg (by linarith only [hc]) ht))
  have units : c^2-r^2=c^2*t^2-s^2*r^2 := by
    have one := congrArg (fun x : ℝ => x*c^2) ru
    have two := congrArg (fun x : ℝ => x*r^2) au
    dsimp at one two
    nlinarith only [one,two]
  have cr : c ≤ r := by
    by_contra failure
    have positive := mul_pos (sub_pos.mpr (lt_of_not_ge failure))
      (show 0 < c+r by linarith only [hc,hr])
    nlinarith only [squareOrder,units,positive]
  have ts : t ≤ s := by
    by_contra failure
    have positive := mul_pos (sub_pos.mpr (lt_of_not_ge failure))
      (show 0 < t+s by linarith only [ht,hs,lt_of_not_ge failure])
    have other := mul_nonneg (sub_nonneg.mpr cr)
      (show 0 ≤ r+c by linarith only [hr,hc])
    nlinarith only [positive,other,au,ru]
  have half : t ≤ (1+r)*z := by
    nlinarith only [angle,ts,mul_nonneg hz (sub_nonneg.mpr cr)]
  have lower := mul_le_mul_of_nonneg_left half (mul_nonneg hr.le ht)
  have upper := mul_lt_mul_of_pos_left wall (show 0 < 1+r by linarith only [hr])
  have margin := mul_nonneg (sq_nonneg t)
    (show 0 ≤ (543/500)*r-457/500 by linarith only [hc,cr])
  nlinarith only [lower,upper,ru,margin]

/-- A point of each genuine square lies in the other's transverse strip.
Therefore only the two forward longitudinal separating axes survive. -/
theorem alternatives (A R : OpenSquare)
    (ha : 1 < A.side) (same : A.side=R.side)
    (ac : 0 < A.c) (aNonneg : 0 ≤ A.s) (narrow : 12*A.s ≤ 5*A.c)
    (rc : 0 < R.c) (rs : 0 ≤ R.s)
    (aq : A.Inside (113/50) 2)
    (gv : -(47/20)*A.s+(33/20)*A.c ≤ A.loV)
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (z : ℝ) (hz : 0 ≤ z) (zhi : z < 2/5)
    (crossing : A.Inside 3 (2+z))
    (apart : ∀ x y, ¬ (A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side ≤ lower R A.c A.s ∨ upper A R.c R.s ≤ R.loU := by
  have acu : A.c ≤ 1 := by nlinarith only [A.unit_normal,sq_nonneg A.s,ac]
  have highVlo : A.loV < -A.s*3+A.c*(12/5) := by
    linarith only [aq.2.2.1,narrow,ac]
  have highVhi : -A.s*3+A.c*(12/5) < A.loV+A.side := by
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

#print axioms wall_angle_order
#print axioms alternatives
end N12Compact.CentralWallPairAxes
