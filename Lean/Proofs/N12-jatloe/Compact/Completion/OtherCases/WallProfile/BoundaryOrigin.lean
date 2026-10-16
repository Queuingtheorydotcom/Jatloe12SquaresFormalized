import Compact.Completion.OtherCases.WallProfile.CornerProfile
import Compact.Completion.OtherCases.WallProfile.BoundaryCapGeometry

/-! All-angle direct origin transfer between two actual congruent squares.
The genuine corner segment supplies the missing vertex bound, and the
matching full-square profile and cap exclude every separating face axis.
This is Theorem7 of C1092-DIRECT-WALL-POINT. -/
namespace N12Compact.Completion.OtherCases.WallProfile
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C1092WallProfileScalars
set_option Elab.async false

private theorem negative_transfer (B K : OpenSquare) (t b ell : ℝ)
    (signed : B.s = -t) (pp : 0 < B.c) (tp : 0 < t)
    (side : 1 < B.side) (same : B.side=K.side)
    (bottomWall : ∀ x y, B.Inside x y → 0 ≤ y)
    (bPositive : 0 < b) (bSmall : b < 1)
    (ellLarge : 1 < ell) (ellSmall : ell < 2)
    (marker : B.Inside 2 b) (inner : B.Inside ell 1)
    (cornerMarker : K.Inside 1 b) (cornerPoint : K.Inside 1 1)
    (profileK : ∀ c s : ℝ, 0 ≤ c → 0 ≤ s → c^2+s^2=1 →
      K.side*profile c s ≤ upper K c (-s))
    (apart : ∀ x y, ¬(K.Inside x y ∧ B.Inside x y)) :
    B.Inside 2 1 := by
  by_contra missing
  have normal : B.c^2+t^2=1 := by simpa only [signed,neg_sq] using B.unit_normal
  have pOne : B.c ≤ 1 := by
    nlinarith only [normal,sq_nonneg t,sq_nonneg (B.c-1)]
  have tOne : t ≤ 1 := by
    nlinarith only [normal,sq_nonneg B.c,sq_nonneg (t-1)]
  have m := marker
  have l := inner
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one] at m l
  have innerWeight := mul_pos pp (sub_pos.mpr ellSmall)
  have markerWeight := mul_pos tp (sub_pos.mpr bSmall)
  have innerVWeight := mul_pos tp (sub_pos.mpr ellSmall)
  have upperFace : B.loV+B.side ≤ 2*t+B.c := by
    apply le_of_not_gt
    intro high
    apply missing
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [l.1,innerWeight]
    · nlinarith only [m.2.1,markerWeight]
    · nlinarith only [l.2.2.1,innerVWeight]
    · linarith only [high]
  let X := B.c*B.loU+t*B.loV
  let Y := -t*B.loU+B.c*B.loV
  have uCoordinate : B.c*X-t*Y=B.loU := by
    dsimp only [X,Y]
    linear_combination B.loU*normal
  have vCoordinate : t*X+B.c*Y=B.loV := by
    dsimp only [X,Y]
    linear_combination B.loV*normal
  have closed : ClosedInside B X Y := by
    have h := vertex B B.loU B.loV
      ⟨le_rfl,by linarith only [B.side_pos]⟩
      ⟨le_rfl,by linarith only [B.side_pos]⟩
    rw [signed] at h
    convert h using 1 <;> dsimp only [X,Y] <;> ring
  have wall := lower_wall_vertex B bottomWall
  have yWall : B.side*t ≤ Y := by
    rw [signed] at wall
    dsimp only [Y]
    nlinarith only [wall]
  have xSmall : X < 1 := by
    have wallWeight := mul_nonneg pp.le (sub_nonneg.mpr yWall)
    have extra := mul_pos (sub_pos.mpr side)
      (show 0 < 1+B.c*t by
        have positive := mul_pos pp tp
        linarith only [positive])
    have remainder := mul_nonneg (sub_nonneg.mpr pOne) (sub_nonneg.mpr tOne)
    have scaled : t*X < t*1 := by
      nlinarith only [upperFace,vCoordinate,wallWeight,extra,remainder]
    exact (mul_lt_mul_iff_right₀ tp).mp scaled
  have yBelowOne : Y < 1 := by
    by_contra high
    have first := mul_pos pp (sub_pos.mpr xSmall)
    have last := mul_nonneg tp.le (show 0 ≤ Y-1 by linarith only [high])
    have ellU := mul_pos pp (sub_pos.mpr ellLarge)
    have ellV := mul_pos tp (sub_pos.mpr ellLarge)
    have duplicate : B.Inside 1 1 := by
      simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
      refine ⟨?_,?_,?_,?_⟩
      · nlinarith only [uCoordinate,first,last]
      · nlinarith only [l.2.1,ellU]
      · linarith only [upperFace,tOne,side]
      · nlinarith only [l.2.2.2,ellV]
    exact apart 1 1 ⟨cornerPoint,duplicate⟩
  have foreignBar : ∀ y : ℝ, b ≤ y → y ≤ 1 → K.Inside 1 y :=
    vertical_owned K 1 b 1 bSmall cornerMarker cornerPoint
  have yBelowMarker : Y < b := by
    by_contra low
    have yl : b ≤ Y := le_of_not_gt low
    let weight := (1-X)/(ell-X)
    have denominator : 0 < ell-X := by linarith only [xSmall,ellLarge]
    have positive : 0 < weight := div_pos (sub_pos.mpr xSmall) denominator
    have small : weight < 1 :=
      (div_lt_one denominator).mpr (by linarith only [ellLarge])
    have relation : weight*(ell-X)=1-X := div_mul_cancel₀ _ denominator.ne'
    let z := (1-weight)*Y+weight
    have xIdentity : (1-weight)*X+weight*ell=1 := by nlinarith only [relation]
    have point := strict_closed_segment B X Y ell 1 weight closed inner positive small
    have lower : b ≤ z := by
      have first := mul_nonneg (show 0 ≤ 1-weight by linarith only [small])
        (sub_nonneg.mpr yl)
      have last := mul_nonneg positive.le (sub_nonneg.mpr bSmall.le)
      dsimp only [z]
      nlinarith only [first,last]
    have upper : z ≤ 1 := by
      have product := mul_nonneg (show 0 ≤ 1-weight by linarith only [small])
        (sub_nonneg.mpr yBelowOne.le)
      dsimp only [z]
      nlinarith only [product]
    have duplicate : B.Inside 1 z := by
      simpa only [xIdentity,mul_one,z] using point
    exact apart 1 z ⟨foreignBar z lower upper,duplicate⟩
  have directed (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (separation : upper K nx ny ≤ lower B nx ny) : False := by
    have nearK := strict_bounds K 1 b nx ny unit cornerMarker
    have nearB := strict_bounds B 2 b nx ny unit marker
    have nxPositive : 0 < nx := by linarith only [nearK.2,nearB.1,separation]
    have nyNegative : ny < 0 := by
      by_contra nonnegative
      have vertexBound := (closed_bounds B X Y nx ny closed).1
      have topK := (strict_bounds K 1 1 nx ny unit cornerPoint).2
      have first := mul_pos nxPositive (sub_pos.mpr xSmall)
      have last := mul_nonneg (le_of_not_gt nonnegative)
        (show 0 ≤ 1-Y by linarith only [yBelowMarker,bSmall])
      nlinarith only [vertexBound,topK,first,last,separation]
    have normal' : nx^2+(-ny)^2=1 := by simpa only [neg_sq] using unit
    have profileBound := profileK nx (-ny) nxPositive.le
      (by linarith only [nyNegative]) normal'
    rw [←same] at profileBound
    have cap := negative_boundary_cap B t nx (-ny) signed pp tp side bottomWall upperFace
      nxPositive (by linarith only [nyNegative]) normal'
    simp only [neg_neg] at profileBound cap
    linarith only [profileBound,cap,separation]
  have reject (nx ny R : ℝ)
      (unit : nx^2+ny^2=1)
      (radius : supportRadius K nx ny+supportRadius B nx ny=R)
      (axis : R ≤ |nx*(centerX B-centerX K)+ny*(centerY B-centerY K)|) : False := by
    have sep := separated K B nx ny (by rwa [radius])
    rcases sep with forward | backward
    · exact directed nx ny unit forward
    · have reversed : upper K (-nx) (-ny) ≤ lower B (-nx) (-ny) := by
        rw [upper_neg,lower_neg]
        linarith only [backward]
      exact directed (-nx) (-ny) (by simpa only [neg_sq] using unit) reversed
  have axes := CongruentSAT.faceSeparation_of_disjoint K B same.symm apart
  change pairRadius K B ≤ |K.c*(centerX B-centerX K)+K.s*(centerY B-centerY K)| ∨
    pairRadius K B ≤ |-K.s*(centerX B-centerX K)+K.c*(centerY B-centerY K)| ∨
    pairRadius B K ≤ |B.c*(centerX B-centerX K)+B.s*(centerY B-centerY K)| ∨
    pairRadius B K ≤ |-B.s*(centerX B-centerX K)+B.c*(centerY B-centerY K)| at axes
  rcases axes with ku | kv | bu | bv
  · exact reject K.c K.s _ K.unit_normal (parallel_radius K B) ku
  · exact reject (-K.s) K.c _ (by nlinarith only [K.unit_normal])
      (transverse_radius K B) kv
  · have radius : supportRadius K B.c B.s+supportRadius B B.c B.s=pairRadius B K := by
      rw [add_comm]; exact parallel_radius B K
    exact reject B.c B.s _ B.unit_normal radius bu
  · have radius : supportRadius K (-B.s) B.c+supportRadius B (-B.s) B.c=pairRadius B K := by
      rw [add_comm]; exact transverse_radius B K
    exact reject (-B.s) B.c _ (by nlinarith only [B.unit_normal]) radius bv

/-- Direct wall-origin transfer from the actual corner's full support profile.
The strict corner segment rules out every vertex crossing. The profile premise
is universal over all first-quadrant unit directions, including the axes. -/
theorem boundary_origin_of_profile (B K : OpenSquare) (b ell : ℝ)
    (side : 1 < B.side) (same : B.side=K.side)
    (bottomWall : ∀ x y, B.Inside x y → 0 ≤ y)
    (bPositive : 0 < b) (bSmall : b < 1)
    (ellLarge : 1 < ell) (ellSmall : ell < 2)
    (marker : B.Inside 2 b) (inner : B.Inside ell 1)
    (cornerMarker : K.Inside 1 b) (cornerPoint : K.Inside 1 1)
    (profileK : ∀ c s : ℝ, 0 ≤ c → 0 ≤ s → c^2+s^2=1 →
      K.side*profile c s ≤ upper K c (-s))
    (apart : ∀ x y, ¬(K.Inside x y ∧ B.Inside x y)) :
    B.Inside 2 1 := by
  obtain ⟨r,pp,sn,shape,inside⟩ := negative_frame B
  have marker' := (inside _ _).mpr marker
  have inner' := (inside _ _).mpr inner
  apply (inside _ _).mp
  by_cases axis : r.s=0
  · simp only [OpenSquare.Inside,InBands,axis,mul_zero,zero_mul,neg_zero,
      zero_add,add_zero,mul_one] at marker' inner' ⊢
    exact ⟨marker'.1,marker'.2.1,inner'.2.2.1,inner'.2.2.2⟩
  · have positive : 0 < -r.s := neg_pos.mpr (lt_of_le_of_ne sn axis)
    have wall' : ∀ x y, r.Inside x y → 0 ≤ y :=
      fun x y h => bottomWall x y ((inside x y).mp h)
    have apart' : ∀ x y, ¬(K.Inside x y ∧ r.Inside x y) :=
      fun x y h => apart x y ⟨h.1,(inside x y).mp h.2⟩
    exact negative_transfer r K (-r.s) b ell (by ring) pp positive
      (by simpa only [shape] using side) (shape.trans same) wall'
      bPositive bSmall ellLarge ellSmall marker' inner' cornerMarker cornerPoint
      profileK apart'

/-- The complete direct wall-origin theorem. The actual corner's excluded
upper point supplies its full profile; the actual corner's strict segment
rules out every vertex crossing. Both square orientations are unrestricted. -/
theorem boundary_origin (B K : OpenSquare) (b ell : ℝ)
    (side : 1 < B.side) (same : B.side=K.side)
    (bottomWall : ∀ x y, B.Inside x y → 0 ≤ y)
    (cornerWalls : ∀ x y, K.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (bPositive : 0 < b) (bSmall : b < 1)
    (ellLarge : 1 < ell) (ellSmall : ell < 2)
    (marker : B.Inside 2 b) (inner : B.Inside ell 1)
    (cornerMarker : K.Inside 1 b) (cornerPoint : K.Inside 1 1)
    (missingUpper : ¬K.Inside 1 (3/2))
    (apart : ∀ x y, ¬(K.Inside x y ∧ B.Inside x y)) :
    B.Inside 2 1 := by
  apply boundary_origin_of_profile B K b ell side same bottomWall
    bPositive bSmall ellLarge ellSmall marker inner cornerMarker cornerPoint
    (fun c s cn sn unit => ?_) apart
  exact corner_profile K (by simpa only [←same] using side)
    cornerWalls cornerPoint missingUpper c s cn sn unit

#print axioms boundary_origin_of_profile
#print axioms boundary_origin
end N12Compact.Completion.OtherCases.WallProfile

