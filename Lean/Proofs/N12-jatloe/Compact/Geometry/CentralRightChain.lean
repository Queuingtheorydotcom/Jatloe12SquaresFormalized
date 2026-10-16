import Compact.Geometry.CentralRightMixedTransfer
import Compact.Geometry.PairedCornerPositiveWall

/-! The complete positive-frame B/R support selector is reduced to the
genuine inward lower-U escape of R. Every original separating axis is
retained until its actual strict points exclude it. -/
namespace N12Compact.CentralRightChain

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977ChainBridge C977CornerCubic
set_option Elab.async false

theorem alternatives (B R : OpenSquare)
    (bn : Normal B.c B.s) (rn : Normal R.c R.s) (same : B.side=R.side)
    (inner : B.Inside (113/50) 2) (low : B.Inside 3 (87/50))
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(B.Inside x y ∧ R.Inside x y)) :
    B.loU+B.side≤lower R B.c B.s ∨ upper B R.c R.s≤R.loU := by
  have bb := normal_bounds bn
  have rb := normal_bounds rn
  have forward (c s : ℝ) (positive : 0<c) (unit : c^2+s^2=1)
      (sep : upper B c s≤lower R c s ∨ upper R c s≤lower B c s) :
      upper B c s≤lower R c s := by
    rcases sep with yes | no
    · exact yes
    · have bp := strict_bounds B _ _ c s unit inner
      have rp := strict_bounds R _ _ c s unit marker
      exfalso
      nlinarith only [no,bp.1,rp.2,positive]
  have transverse (c s : ℝ) (positive : 0<c) (sign : 0≤s)
      (unit : c^2+s^2=1)
      (sep : upper B (-s) c≤lower R (-s) c ∨
        upper R (-s) c≤lower B (-s) c) : False := by
    have normal : (-s)^2+c^2=1 := by nlinarith only [unit]
    rcases sep with forward | reverse
    · have bp := strict_bounds B _ _ (-s) c normal inner
      have rp := strict_bounds R _ _ (-s) c normal marker
      nlinarith only [forward,bp.2,rp.1,sign]
    · have bp := strict_bounds B _ _ (-s) c normal low
      have rp := strict_bounds R _ _ (-s) c normal high
      nlinarith only [reverse,bp.1,rp.2,positive]
  have axes := CongruentSAT.faceSeparation_of_disjoint B R same apart
  change pairRadius B R≤|B.c*(centerX R-centerX B)+B.s*(centerY R-centerY B)| ∨
    pairRadius B R≤|-B.s*(centerX R-centerX B)+B.c*(centerY R-centerY B)| ∨
    pairRadius R B≤|R.c*(centerX R-centerX B)+R.s*(centerY R-centerY B)| ∨
    pairRadius R B≤|-R.s*(centerX R-centerX B)+R.c*(centerY R-centerY B)| at axes
  have separateAxis (nx ny K : ℝ)
      (identity : supportRadius B nx ny+supportRadius R nx ny=K)
      (sep : K≤|nx*(centerX R-centerX B)+ny*(centerY R-centerY B)|) :=
    separated B R nx ny (by rwa [identity])
  rcases axes with bu | bv | ru | rv
  · left
    have h := forward B.c B.s (by linarith only [bb.1]) B.unit_normal
      (separateAxis _ _ _ (parallel_radius B R) bu)
    simpa only [(ownU B).2] using h
  · exact False.elim (transverse B.c B.s (by linarith only [bb.1]) bn.1 B.unit_normal
      (separateAxis _ _ _ (transverse_radius B R) bv))
  · right
    have identity : supportRadius B R.c R.s+supportRadius R R.c R.s=pairRadius R B := by
      rw [add_comm]; exact parallel_radius R B
    have h := forward R.c R.s (by linarith only [rb.1]) R.unit_normal
      (separateAxis _ _ _ identity ru)
    simpa only [(ownU R).1] using h
  · have identity : supportRadius B (-R.s) R.c+supportRadius R (-R.s) R.c=
        pairRadius R B := by
      rw [add_comm]; exact transverse_radius R B
    exact False.elim (transverse R.c R.s (by linarith only [rb.1]) rn.1 R.unit_normal
      (separateAxis _ _ _ identity rv))

/-- Both longitudinal axes and the full relative-angle arc have been
handled. The conclusion is a strict real wall displacement, not a whole
packing exclusion or an assumed missing point. -/
theorem lower_shift (B R : OpenSquare)
    (bn : Normal B.c B.s) (rn : Normal R.c R.s)
    (same : B.side=R.side) (side : 1<B.side) (box : InsideContainer R)
    (bMarker : B.Inside (47/20) (33/20))
    (inner : B.Inside (113/50) 2) (low : B.Inside 3 (87/50))
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (corner : ¬R.Inside 3 3)
    (apart : ∀ x y, ¬(B.Inside x y ∧ R.Inside x y))
    (start : 2*(B.c+B.s)≤B.loU) :
    3*R.c+2*R.s<R.loU := by
  have rSide : 1≤R.side := by simpa only [←same] using side.le
  rcases alternatives B R bn rn same inner low marker high apart with own | wall
  · have bound := CentralRightCornerSupport.lower_support R bn rn rSide box marker corner
    exfalso
    linarith only [bound,start,side,own]
  · by_cases order : 0≤B.c*R.s-B.s*R.c
    · exact CentralRightMixedTransfer.steeper_wall_shift B R bn rn side inner start order wall
    · have reach := CentralRightMixedTransfer.shallower_reach B bn rn side bMarker start
        (by linarith only [order])
      have bound := CentralRightCornerSupport.lower_support R rn rn rSide box marker corner
      rw [(ownU R).1] at bound
      exfalso
      linarith only [reach,bound,wall]

theorem negative_alternatives (B R : OpenSquare) (t : ℝ)
    (bn : Normal B.c B.s) (rn : Normal R.c t) (signed : R.s=-t)
    (same : B.side=R.side)
    (inner : B.Inside (113/50) 2) (low : B.Inside 3 (87/50))
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (apart : ∀ x y, ¬(B.Inside x y ∧ R.Inside x y)) :
    B.loU+B.side≤lower R B.c B.s ∨ upper B t R.c≤R.loV := by
  have bb := normal_bounds bn
  have rb := normal_bounds rn
  have bc : 0<B.c := by linarith only [bb.1]
  have rc : 0<R.c := by linarith only [rb.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint B R same apart
  change pairRadius B R≤|B.c*(centerX R-centerX B)+B.s*(centerY R-centerY B)| ∨
    pairRadius B R≤|-B.s*(centerX R-centerX B)+B.c*(centerY R-centerY B)| ∨
    pairRadius R B≤|R.c*(centerX R-centerX B)+R.s*(centerY R-centerY B)| ∨
    pairRadius R B≤|-R.s*(centerX R-centerX B)+R.c*(centerY R-centerY B)| at axes
  have separateAxis (nx ny K : ℝ)
      (identity : supportRadius B nx ny+supportRadius R nx ny=K)
      (sep : K≤|nx*(centerX R-centerX B)+ny*(centerY R-centerY B)|) :=
    separated B R nx ny (by rwa [identity])
  have bTransverse : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
  have rTransverse : (-R.s)^2+R.c^2=1 := by nlinarith only [R.unit_normal]
  rcases axes with bu | bv | ru | rv
  · have sep := separateAxis _ _ _ (parallel_radius B R) bu
    rcases sep with forward | reverse
    · left; simpa only [(ownU B).2] using forward
    · have bp := strict_bounds B _ _ B.c B.s B.unit_normal inner
      have rp := strict_bounds R _ _ B.c B.s B.unit_normal marker
      exfalso; nlinarith only [reverse,bp.1,rp.2,bc]
  · have sep := separateAxis _ _ _ (transverse_radius B R) bv
    rcases sep with forward | reverse
    · have bp := strict_bounds B _ _ (-B.s) B.c bTransverse inner
      have rp := strict_bounds R _ _ (-B.s) B.c bTransverse marker
      exfalso; nlinarith only [forward,bp.2,rp.1,bn.1]
    · have bp := strict_bounds B _ _ (-B.s) B.c bTransverse low
      have rp := strict_bounds R _ _ (-B.s) B.c bTransverse high
      exfalso; nlinarith only [reverse,bp.1,rp.2,bc]
  · have identity : supportRadius B R.c R.s+supportRadius R R.c R.s=pairRadius R B := by
      rw [add_comm]; exact parallel_radius R B
    have sep := separateAxis _ _ _ identity ru
    rcases sep with forward | reverse
    · have bp := strict_bounds B _ _ R.c R.s R.unit_normal low
      have rp := strict_bounds R _ _ R.c R.s R.unit_normal high
      exfalso; nlinarith only [forward,bp.2,rp.1,signed,rn.1]
    · have bp := strict_bounds B _ _ R.c R.s R.unit_normal inner
      have rp := strict_bounds R _ _ R.c R.s R.unit_normal marker
      exfalso; nlinarith only [reverse,bp.1,rp.2,rc]
  · have identity : supportRadius B (-R.s) R.c+supportRadius R (-R.s) R.c=
        pairRadius R B := by
      rw [add_comm]; exact transverse_radius R B
    have sep := separateAxis _ _ _ identity rv
    rcases sep with forward | reverse
    · right
      rw [(ownV R).1] at forward
      simpa only [signed,neg_neg] using forward
    · have bp := strict_bounds B _ _ (-R.s) R.c rTransverse low
      have rp := strict_bounds R _ _ (-R.s) R.c rTransverse high
      exfalso; nlinarith only [reverse,bp.1,rp.2,rc]

/-- The other right-wall sign is completely excluded by the actual
paired upper corner. Its full square and outward point are retained. -/
theorem negative_impossible (B R E : OpenSquare) (t : ℝ)
    (bn : Normal B.c B.s) (rn : Normal R.c t) (signed : R.s=-t) (positive : 0<t)
    (same : B.side=R.side) (side : 1<B.side) (box : InsideContainer R)
    (inner : B.Inside (113/50) 2) (low : B.Inside 3 (87/50))
    (marker : R.Inside (1543/500) 2) (high : R.Inside 3 (12/5))
    (outward : E.Inside (16/5) 3) (corner : E.Inside 3 3)
    (right : E.Inside (1543/500) 3) (top : E.Inside 3 (1543/500))
    (br : ∀ x y, ¬(B.Inside x y ∧ R.Inside x y))
    (er : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y))
    (start : 2*(B.c+B.s)≤B.loU) : False := by
  have rb := normal_bounds rn
  have rc : 0≤R.c := by linarith only [rb.1]
  have rSide : 1<R.side := by simpa only [←same] using side
  rcases negative_alternatives B R t bn rn signed same inner low marker high br with own | wall
  · have bound := CentralRightCornerSupport.negative_lower_support R bn rn signed
      rSide.le box marker
    linarith only [bound,start,side,own]
  · have first := mul_nonneg rc (sub_nonneg.mpr bn.2.1)
    have second := mul_nonneg bn.1 (sub_nonneg.mpr rn.2.1)
    have order : 0≤B.c*R.c-B.s*t := by nlinarith only [first,second]
    have reach := CentralRightMixedTransfer.steeper_direction_reach B bn positive rc
      side inner start order
    have lower : 3*t+2*R.c≤R.loV := by linarith only [reach,wall]
    exact PairedCornerPositiveWall.negative_right_impossible R E t signed rn rSide box
      marker high lower outward corner right top er

#print axioms alternatives
#print axioms lower_shift
#print axioms negative_alternatives
#print axioms negative_impossible
end N12Compact.CentralRightChain
