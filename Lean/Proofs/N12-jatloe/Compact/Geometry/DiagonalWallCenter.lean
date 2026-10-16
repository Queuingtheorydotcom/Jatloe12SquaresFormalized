import Compact.Geometry.DiagonalWallSegment
import Compact.Geometry.ABTransverse

/-! A diagonal-owning wall has only one shallow signed orientation.
The elbow's two compulsory outer arms then rule out all its separating
axes in the remaining near-vertical sector.  The corner exclusion is
an actual foreign point, and the original side upper bound is explicit. -/
namespace N12Compact.DiagonalWallCenter

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic C977ChainBridge
set_option Elab.async false

/-- The diagonal and the marker select a strictly negative canonical
wall frame.  The genuine foreign corner is needed to remove the positive
frame; the marker-to-diagonal width bounds the negative tilt. -/
theorem wall_frame (R : OpenSquare) (hc : 0<R.c) (canonical : |R.s|≤R.c)
    (size : R.side≤1001/1000)
    (marker : R.Inside (1543/500) 2)
    (right : R.Inside 3 (12/5)) (top : R.Inside (12/5) 3)
    (corner : ¬R.Inside 3 3) : R.s<0 ∧ -2*R.s<R.c := by
  have signed := abs_le.mp canonical
  have negative : R.s<0 := by
    by_contra failure
    have hs : 0≤R.s := le_of_not_gt failure
    have normal : Normal R.c R.s := ⟨hs,signed.2,R.unit_normal⟩
    have bounds := normal_bounds normal
    have cap : R.loU+R.side≤3*R.c+3*R.s := by
      apply le_of_not_gt
      intro high
      apply corner
      refine ⟨?_,?_,?_,?_⟩
      · nlinarith only [right.1,hs]
      · nlinarith only [high]
      · nlinarith only [marker.2.2.1,hc,hs]
      · nlinarith only [top.2.2.2,hs]
    have slope : (43/500)*R.c<R.s := by
      linarith only [marker.2.1,cap]
    have width : R.c+(343/500)*R.s<1001/1000 := by
      linarith only [marker.2.2.1,top.2.2.2,size]
    have square := mul_nonneg (sub_nonneg.mpr width.le)
      (show 0≤1001/1000+(R.c+(343/500)*R.s) by
        linarith only [hc,hs])
    have cross := mul_pos hc (sub_pos.mpr slope)
    have ordered := mul_nonneg hs (sub_nonneg.mpr signed.2)
    have cosine := mul_nonneg (sub_nonneg.mpr bounds.1)
      (show 0≤R.c+7/10 by linarith only [hc])
    nlinarith only [square,cross,ordered,cosine,R.unit_normal]
  refine ⟨negative,?_⟩
  let t := -R.s
  have ht : 0≤t := by dsimp [t]; linarith only [negative]
  have normal : Normal R.c t := by
    refine ⟨ht,?_,?_⟩
    · dsimp [t]; linarith only [signed.1]
    · dsimp [t]; nlinarith only [R.unit_normal]
  have bounds := normal_bounds normal
  have width : (343/500)*R.c+t<1001/1000 := by
    dsimp [t]
    linarith only [top.1,marker.2.1,size]
  have square := mul_nonneg (sub_nonneg.mpr width.le)
    (show 0≤1001/1000+((343/500)*R.c+t) by linarith only [hc,ht])
  have cosine := mul_nonneg (sub_nonneg.mpr bounds.1)
    (show 0≤R.c+7/10 by linarith only [hc])
  by_contra failure
  have slope : R.c≤2*t := by dsimp [t]; linarith only [le_of_not_gt failure]
  have product := mul_nonneg hc.le (sub_nonneg.mpr slope)
  nlinarith only [square,cosine,product,normal.2.2]

/-- Four genuine strict points remove every SAT direction when both
physical squares have shallow negative face frames.  No guessed
separator or stored enclosure enters this argument. -/
theorem negative_pair_impossible (A R : OpenSquare)
    (ac : 0<A.c) (asign : A.s≤0) (anarrow : -2*A.s≤A.c)
    (rc : 0<R.c) (rsign : R.s≤0) (rnarrow : -2*R.s≤R.c)
    (same : A.side=R.side)
    (inner : A.Inside (113/50) 2)
    (outerRight : A.Inside (53/20) (47/20))
    (outerTop : A.Inside (47/20) (53/20))
    (marker : R.Inside (1543/500) 2) (top : R.Inside (12/5) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) : False := by
  have longitudinal (c s : ℝ) (positive : 0<c) (nonpositive : s≤0)
      (unit : c^2+s^2=1)
      (sep : upper A c s≤lower R c s ∨ upper R c s≤lower A c s) : False := by
    rcases sep with forward | reverse
    · have a := strict_bounds A _ _ c s unit outerRight
      have r := strict_bounds R _ _ c s unit top
      nlinarith only [forward,a.2,r.1,positive,nonpositive]
    · have a := strict_bounds A _ _ c s unit inner
      have r := strict_bounds R _ _ c s unit marker
      nlinarith only [reverse,a.1,r.2,positive]
  have transverse (c s : ℝ) (positive : 0<c) (nonpositive : s≤0)
      (narrow : -2*s≤c) (unit : c^2+s^2=1)
      (sep : upper A (-s) c≤lower R (-s) c ∨
        upper R (-s) c≤lower A (-s) c) : False := by
    have normal : (-s)^2+c^2=1 := by nlinarith only [unit]
    rcases sep with forward | reverse
    · have a := strict_bounds A _ _ (-s) c normal outerTop
      have r := strict_bounds R _ _ (-s) c normal marker
      nlinarith only [forward,a.2,r.1,positive,narrow]
    · have a := strict_bounds A _ _ (-s) c normal inner
      have r := strict_bounds R _ _ (-s) c normal top
      nlinarith only [reverse,a.1,r.2,positive,nonpositive]
  have axes := CongruentSAT.faceSeparation_of_disjoint A R same apart
  change pairRadius A R≤|A.c*(centerX R-centerX A)+A.s*(centerY R-centerY A)| ∨
    pairRadius A R≤|-A.s*(centerX R-centerX A)+A.c*(centerY R-centerY A)| ∨
    pairRadius R A≤|R.c*(centerX R-centerX A)+R.s*(centerY R-centerY A)| ∨
    pairRadius R A≤|-R.s*(centerX R-centerX A)+R.c*(centerY R-centerY A)| at axes
  have separateAxis (nx ny radius : ℝ)
      (identity : supportRadius A nx ny+supportRadius R nx ny=radius)
      (sep : radius≤|nx*(centerX R-centerX A)+ny*(centerY R-centerY A)|) :=
    separated A R nx ny (by rwa [identity])
  rcases axes with au | av | ru | rv
  · exact longitudinal A.c A.s ac asign A.unit_normal
      (separateAxis _ _ _ (parallel_radius A R) au)
  · exact transverse A.c A.s ac asign anarrow A.unit_normal
      (separateAxis _ _ _ (transverse_radius A R) av)
  · have identity : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]; exact parallel_radius R A
    exact longitudinal R.c R.s rc rsign R.unit_normal (separateAxis _ _ _ identity ru)
  · have identity : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]; exact transverse_radius R A
    exact transverse R.c R.s rc rsign rnarrow R.unit_normal
      (separateAxis _ _ _ identity rv)

/-- Whole all-angle elbow conclusion with the actual diagonal wall.
Its foreign corner is derived by the original-packing adapter, rather
than inferred from a missing auxiliary index. -/
theorem point (A R : OpenSquare) (ha : 1<A.side)
    (same : A.side=R.side) (size : R.side≤1001/1000) (box : InsideContainer R)
    (p : A.Inside 2 (113/50)) (q : A.Inside (113/50) 2)
    (m : A.Inside (47/20) (47/20))
    (missingG : ¬A.Inside (47/20) (33/20))
    (missingB : ¬A.Inside (33/20) (47/20))
    (marker : R.Inside (1543/500) 2)
    (right : R.Inside 3 (12/5)) (top : R.Inside (12/5) 3)
    (corner : ¬R.Inside 3 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) : A.Inside 2 2 := by
  obtain ⟨a,hc,hs,side,inside,_⟩ := ClosedFrames.positive_frame A
  have ha' : 1<a.side := by simpa only [side] using ha
  have same' : a.side=R.side := side.trans same
  have ap := (inside _ _).mpr p
  have aq := (inside _ _).mpr q
  have am := (inside _ _).mpr m
  have g : ¬a.Inside (47/20) (33/20) := fun h => missingG ((inside _ _).mp h)
  have b : ¬a.Inside (33/20) (47/20) := fun h => missingB ((inside _ _).mp h)
  have ar : ∀ x y, ¬(a.Inside x y ∧ R.Inside x y) :=
    fun x y h => apart x y ⟨(inside x y).mp h.1,h.2⟩
  have missingTop := DiagonalWallSegment.missing_top a R aq right top ar
  by_cases shallow : a.s≤a.c
  · exact (inside _ _).mp (CentralWallCenter.shallow a R ha' same' box hc hs shallow
      ap aq am g b (fun h => ar _ _ ⟨h,right⟩) (fun h => ar _ _ ⟨h,top⟩)
      missingTop marker right ar)
  · by_contra missing
    have absent : ¬a.Inside 2 2 := fun h => missing ((inside _ _).mp h)
    have steep : a.c≤a.s := (lt_of_not_ge shallow).le
    by_cases middle : a.s≤2*a.c
    · exact DiagonalWallSegment.middle_impossible a R ha' hc hs steep middle
        ap aq am absent right top ar
    · have arms := CentralOuterReach.points a ha' ap aq am g b
        (fun h => ar _ _ ⟨h,right⟩) (fun h => ar _ _ ⟨h,top⟩)
      obtain ⟨W,wc,wn,wsame,winside,_⟩ := ClosedFrames.canonical_frame R
      have wm := (winside _ _).mpr marker
      have wr := (winside _ _).mpr right
      have wt := (winside _ _).mpr top
      have frame := wall_frame W wc wn (by simpa only [wsame] using size)
        wm wr wt (fun h => corner ((winside _ _).mp h))
      let a' := turnFrame (turnFrame (turnFrame a))
      have equivalent (x y : ℝ) : a'.Inside x y↔a.Inside x y := by
        dsimp [a']; simp only [turnFrame_inside]
      have same'' : a'.side=W.side := by
        dsimp [a']; simpa using same'.trans wsame.symm
      exact negative_pair_impossible a' W
        (by dsimp [a',turnFrame]; linarith only [hc,steep])
        (by dsimp [a',turnFrame]; linarith only [hc])
        (by dsimp [a',turnFrame]; linarith only [lt_of_not_ge middle])
        wc frame.1.le frame.2.le same''
        ((equivalent _ _).mpr aq) ((equivalent _ _).mpr arms.2)
        ((equivalent _ _).mpr arms.1) wm wt
        (fun x y h => ar x y ⟨(equivalent x y).mp h.1,(winside x y).mp h.2⟩)

#print axioms wall_frame
#print axioms negative_pair_impossible
#print axioms point
end N12Compact.DiagonalWallCenter
