import Compact.Completion.C1092.TwoFifthsData

/-! Whole-square supports and the exhaustive directed separator sources
for the two-fifths squeeze. Strict anchors remove leftward and vertical
directions; weak support separation, including legal contact, is retained. -/
namespace N12Compact.C1092TwoFifths.Support
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C1092WholeSupports
set_option Elab.async false
noncomputable section

theorem upper_pos_pos (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : 0≤d) (en : 0≤e) :
    upper Q nx ny=d*(Q.loU+Q.side)+e*(Q.loV+Q.side) := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_left dn,max_eq_left en]
  ring

theorem upper_pos_neg (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : 0≤d) (en : e≤0) :
    upper Q nx ny=d*(Q.loU+Q.side)+e*Q.loV := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_left dn,max_eq_right en]
  ring

theorem upper_neg_neg (Q : OpenSquare) (nx ny d e : ℝ)
    (du : nx*Q.c+ny*Q.s=d) (dv : -nx*Q.s+ny*Q.c=e)
    (dn : d≤0) (en : e≤0) : upper Q nx ny=d*Q.loU+e*Q.loV := by
  rw [(formulas Q nx ny).2,du,dv,max_eq_right dn,max_eq_right en]
  ring

theorem radius_even (Q : OpenSquare) (nx ny : ℝ) :
    supportRadius Q (-nx) (-ny)=supportRadius Q nx ny := by
  simp only [supportRadius,
    show (-nx)*Q.c+(-ny)*Q.s=-(nx*Q.c+ny*Q.s) by ring,
    show -(-nx)*Q.s+(-ny)*Q.c=-(-nx*Q.s+ny*Q.c) by ring,abs_neg]

theorem upper_neg (Q : OpenSquare) (nx ny : ℝ) :
    upper Q (-nx) (-ny)= -lower Q nx ny := by
  unfold upper lower
  rw [radius_even]
  ring

theorem lower_neg (Q : OpenSquare) (nx ny : ℝ) :
    lower Q (-nx) (-ny)= -upper Q nx ny := by
  unfold lower upper
  rw [radius_even]
  ring

theorem reverse (A R : OpenSquare) (nx ny : ℝ)
    (sep : upper R nx ny≤lower A nx ny) :
    upper A (-nx) (-ny)≤lower R (-nx) (-ny) := by
  rw [upper_neg,lower_neg]
  linarith only [sep]

theorem rightward (A R : OpenSquare) (x y nx ny : ℝ)
    (unit : nx^2+ny^2=1) (first : A.Inside x y)
    (last : R.Inside 1 y) (left : x<1)
    (sep : upper A nx ny≤lower R nx ny) : 0<nx := by
  have f := (strict_bounds A x y nx ny unit first).2
  have l := (strict_bounds R 1 y nx ny unit last).1
  apply lt_of_not_ge
  intro bad
  have product := mul_nonpos_of_nonpos_of_nonneg bad
    (show 0≤1-x by linarith only [left])
  nlinarith only [f,l,sep,product]

private theorem candidates (A R : OpenSquare) (same : A.side=R.side)
    (cp : 0<A.c) (sn : 0≤A.s) (dp : 0<R.c)
    (x y : ℝ) (first : A.Inside x y) (last : R.Inside 1 y) (left : x<1)
    (apart : ∀ x y,¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side≤lower R A.c A.s ∨
      upper A A.s (-A.c)≤lower R A.s (-A.c) ∨
      upper A R.c R.s≤R.loU ∨
      upper A (-R.s) R.c≤R.loV ∨
      upper A R.s (-R.c)≤-(R.loV+R.side) := by
  have axes := CongruentSAT.faceSeparation_of_disjoint A R same apart
  change pairRadius A R≤|A.c*(centerX R-centerX A)+A.s*(centerY R-centerY A)| ∨
    pairRadius A R≤|-A.s*(centerX R-centerX A)+A.c*(centerY R-centerY A)| ∨
    pairRadius R A≤|R.c*(centerX R-centerX A)+R.s*(centerY R-centerY A)| ∨
    pairRadius R A≤|-R.s*(centerX R-centerX A)+R.c*(centerY R-centerY A)| at axes
  have split (nx ny radius : ℝ)
      (eq : supportRadius A nx ny+supportRadius R nx ny=radius)
      (sep : radius≤|nx*(centerX R-centerX A)+ny*(centerY R-centerY A)|) :=
    separated A R nx ny (by rwa [eq])
  have cone := rightward A R x y
  rcases axes with au|av|ru|rv
  · rcases split _ _ _ (parallel_radius A R) au with forward|backward
    · exact Or.inl (by simpa only [(ownU A).2] using forward)
    · have failed := cone (-A.c) (-A.s) (by nlinarith only [A.unit_normal])
        first last left (reverse A R _ _ backward)
      exfalso; linarith only [failed,cp]
  · rcases split _ _ _ (transverse_radius A R) av with forward|backward
    · have failed := cone (-A.s) A.c (by nlinarith only [A.unit_normal])
        first last left forward
      exfalso; linarith only [failed,sn]
    · right; left
      simpa only [neg_neg] using reverse A R _ _ backward
  · have radius : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]; exact parallel_radius R A
    rcases split _ _ _ radius ru with forward|backward
    · right; right; left
      simpa only [(ownU R).1] using forward
    · have failed := cone (-R.c) (-R.s) (by nlinarith only [R.unit_normal])
        first last left (reverse A R _ _ backward)
      exfalso; linarith only [failed,dp]
  · have radius : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]; exact transverse_radius R A
    rcases split _ _ _ radius rv with forward|backward
    · right; right; right; left
      simpa only [(ownV R).1] using forward
    · right; right; right; right
      have result := reverse A R _ _ backward
      have opposite : lower R R.s (-R.c)=-(R.loV+R.side) := by
        simpa only [neg_neg,(ownV R).2] using lower_neg R (-R.s) R.c
      simpa only [neg_neg,opposite] using result

theorem negative_axes (A R : OpenSquare) (same : A.side=R.side)
    (cp : 0<A.c) (sn : 0≤A.s) (dp : 0<R.c) (rn : R.s≤0)
    (x y : ℝ) (first : A.Inside x y) (last : R.Inside 1 y) (left : x<1)
    (apart : ∀ x y,¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side≤lower R A.c A.s ∨
      upper A A.s (-A.c)≤lower R A.s (-A.c) ∨
      upper A R.c R.s≤R.loU ∨ upper A (-R.s) R.c≤R.loV := by
  rcases candidates A R same cp sn dp x y first last left apart with a|b|c|d|e
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr d))
  · have sep : upper A R.s (-R.c)≤lower R R.s (-R.c) := by
      have identity : lower R R.s (-R.c)=-(R.loV+R.side) := by
        simpa only [neg_neg,(ownV R).2] using lower_neg R (-R.s) R.c
      rwa [identity]
    have failed := rightward A R x y R.s (-R.c)
      (by nlinarith only [R.unit_normal]) first last left sep
    exfalso; linarith only [failed,rn]

theorem positive_axes (A R : OpenSquare) (same : A.side=R.side)
    (cp : 0<A.c) (sn : 0≤A.s) (dp : 0<R.c) (rn : 0≤R.s)
    (x y : ℝ) (first : A.Inside x y) (last : R.Inside 1 y) (left : x<1)
    (apart : ∀ x y,¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side≤lower R A.c A.s ∨
      upper A A.s (-A.c)≤lower R A.s (-A.c) ∨
      upper A R.c R.s≤R.loU ∨ upper A R.s (-R.c)≤-(R.loV+R.side) := by
  rcases candidates A R same cp sn dp x y first last left apart with a|b|c|d|e
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · have sep : upper A (-R.s) R.c≤lower R (-R.s) R.c := by
      simpa only [(ownV R).1] using d
    have failed := rightward A R x y (-R.s) R.c
      (by nlinarith only [R.unit_normal]) first last left sep
    exfalso; linarith only [failed,rn]
  · exact Or.inr (Or.inr (Or.inr e))

theorem wall_lower (R : OpenSquare) (h : Right R) (cp : 0≤R.c)
    (nx ny : ℝ) (xn : 0≤nx) (yn : ny≤0) :
    lower R nx ny≤2*nx-R.side*(nx*(R.c+|R.s|)+
      |nx*R.c+ny*R.s|+|-nx*R.s+ny*R.c|)/2 := by
  have wall := square_support_bound R 1 0 2
    (by intro x y own; simpa only [one_mul,zero_mul,add_zero] using h.wall x y own)
  have center : centerX R+R.side/2*(R.c+|R.s|)≤2 := by
    simpa only [squareRadius,one_mul,zero_mul,add_zero,neg_mul,zero_sub,
      abs_neg,abs_of_nonneg cp] using wall
  have first := mul_le_mul_of_nonneg_left center xn
  have last := mul_nonpos_of_nonpos_of_nonneg yn h.center
  dsimp [lower,supportRadius]
  nlinarith only [first,last]

end
#print axioms negative_axes
#print axioms positive_axes
#print axioms wall_lower
end N12Compact.C1092TwoFifths.Support
