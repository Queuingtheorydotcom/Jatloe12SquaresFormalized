import Compact.Geometry.DiagonalWallCenter
import Compact.Geometry.DiagonalOuterElbowBounds

/-! An elbow owning the outer top auxiliary cannot avoid the center beside
the genuine diagonal wall. The proof retains all eight SAT directions.
The steep sector additionally uses one strict point of the top owner. -/
namespace N12Compact.DiagonalOuterElbow
open C977ChainBridge S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977CornerCubic
set_option Elab.async false

private theorem corner (q : OpenSquare) (u v : ℝ)
    (hu : q.loU≤u ∧ u≤q.loU+q.side)
    (hv : q.loV≤v ∧ v≤q.loV+q.side) :
    ClosedInside q (q.c*u-q.s*v) (q.s*u+q.c*v) := by
  have first : q.c*(q.c*u-q.s*v)+q.s*(q.s*u+q.c*v)=u := by
    linear_combination u*q.unit_normal
  have second : -q.s*(q.c*u-q.s*v)+q.c*(q.s*u+q.c*v)=v := by
    linear_combination v*q.unit_normal
  change q.loU≤_ ∧ _≤q.loU+q.side ∧ q.loV≤_ ∧ _≤q.loV+q.side
  rw [first,second]
  exact ⟨hu.1,hu.2,hv.1,hv.2⟩

/-- The actual strict points remove five of the eight directed axes. -/
private theorem alternatives (A R : OpenSquare) (t : ℝ)
    (hc : 0<A.c) (hs : 0≤A.s) (rn : Normal R.c t)
    (rs : R.s=-t) (narrow : 2*t≤R.c) (same : A.side=R.side)
    (p : A.Inside 2 (113/50)) (f : A.Inside (113/50) 3)
    (marker : R.Inside (1543/500) 2) (top : R.Inside (12/5) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) :
    A.loU+A.side≤lower R A.c A.s ∨
      upper R (-A.s) A.c≤A.loV ∨ upper A R.c (-t)≤R.loU := by
  have rc : 0<R.c := by linarith only [(normal_bounds rn).1]
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
  · rcases separateAxis _ _ _ (parallel_radius A R) au with forward | reverse
    · exact Or.inl (by simpa only [(ownU A).2] using forward)
    · have a := (strict_bounds A _ _ A.c A.s A.unit_normal p).1
      have r := (strict_bounds R _ _ A.c A.s A.unit_normal top).2
      exfalso
      nlinarith only [reverse,a,r,hc,hs]
  · have unit : (-A.s)^2+A.c^2=1 := by nlinarith only [A.unit_normal]
    rcases separateAxis _ _ _ (transverse_radius A R) av with forward | reverse
    · have a := (strict_bounds A _ _ (-A.s) A.c unit f).2
      have r := (strict_bounds R _ _ (-A.s) A.c unit marker).1
      exfalso
      nlinarith only [forward,a,r,hc,hs]
    · exact Or.inr (Or.inl (by simpa only [(ownV A).1] using reverse))
  · have identity : supportRadius A R.c R.s+supportRadius R R.c R.s=pairRadius R A := by
      rw [add_comm]; exact parallel_radius R A
    rcases separateAxis _ _ _ identity ru with forward | reverse
    · right; right
      rw [(ownU R).1] at forward
      simpa only [rs] using forward
    · have a := (strict_bounds A _ _ R.c R.s R.unit_normal p).1
      have r := (strict_bounds R _ _ R.c R.s R.unit_normal marker).2
      rw [rs] at reverse a r
      exfalso
      nlinarith only [reverse,a,r,rc,rn.1]
  · have identity : supportRadius A (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R A := by
      rw [add_comm]; exact transverse_radius R A
    have unit : (-R.s)^2+R.c^2=1 := by nlinarith only [R.unit_normal]
    rcases separateAxis _ _ _ identity rv with forward | reverse
    · have a := (strict_bounds A _ _ (-R.s) R.c unit f).2
      have r := (strict_bounds R _ _ (-R.s) R.c unit marker).1
      rw [rs] at forward a r
      exfalso
      nlinarith only [forward,a,r,rc,narrow]
    · have a := (strict_bounds A _ _ (-R.s) R.c unit p).1
      have r := (strict_bounds R _ _ (-R.s) R.c unit top).2
      rw [rs] at reverse a r
      exfalso
      nlinarith only [reverse,a,r,rc,rn.1]

private theorem shallow (A R : OpenSquare) (t : ℝ)
    (ha : 1<A.side) (an : Normal A.c A.s) (rn : Normal R.c t)
    (rs : R.s=-t) (narrow : 2*t≤R.c) (same : A.side=R.side)
    (p : A.Inside 2 (113/50)) (f : A.Inside (113/50) 3)
    (m : A.Inside (47/20) (47/20))
    (missing : ¬A.Inside 2 2) (missingNW : ¬A.Inside (33/20) (47/20))
    (marker : R.Inside (1543/500) 2) (top : R.Inside (12/5) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y)) : False := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have hs := an.1
  have ht := rn.1
  have hc : 0<A.c := by linarith only [ab.1]
  have rc : 0<R.c := by linarith only [rb.1]
  have height : 0≤A.side := by linarith only [ha]
  have rheight : 0≤R.side := by linarith only [height,same]
  have low : 2*A.c+2*A.s≤A.loU ∨ 2*A.c-2*A.s≤A.loV := by
    by_cases hu : 2*A.c+2*A.s≤A.loU
    · exact Or.inl hu
    · right
      apply le_of_not_gt
      intro hv
      apply missing
      refine ⟨by linarith only [lt_of_not_ge hu],?_,by linarith only [hv],?_⟩
      · nlinarith only [m.2.1,hc,an.1]
      · nlinarith only [p.2.2.2,hc]
  have nw (hv : 2*A.c-2*A.s≤A.loV) :
      (33/20)*A.c+(47/20)*A.s≤A.loU := by
    apply le_of_not_gt
    intro hu
    apply missingNW
    refine ⟨by linarith only [hu],?_,?_,?_⟩
    · nlinarith only [m.2.1,hc]
    · nlinarith only [p.2.2.1,hc,an.1]
    · nlinarith only [hv,ha,ab.2.2.2.2.2]
  let K := R.c*A.c-t*A.s
  let H := R.c*A.s+t*A.c
  have kp : 0≤K := by
    have one := mul_nonneg rn.1 (sub_nonneg.mpr an.2.1)
    have two := mul_nonneg hc.le (sub_nonneg.mpr rn.2.1)
    dsimp [K]; nlinarith only [one,two]
  have hp : 0≤H := by
    dsimp [H]; positivity
  have rtop : R.loU<(12/5)*R.c-3*t := by
    have bound := top.1
    rw [rs] at bound
    linarith only [bound]
  have rmarker : R.loV<(1543/500)*t+2*R.c := by
    have bound := marker.2.2.1
    rw [rs] at bound
    linarith only [bound]
  have support (base : ℝ) (face : base≤A.loU) :
      K*(base+1)-H*((47/20)*(A.c-A.s))≤upper A R.c (-t) := by
    have point := corner A (A.loU+A.side) A.loV
      ⟨by linarith only [height],le_rfl⟩ ⟨le_rfl,by linarith only [height]⟩
    have bound := (closed_bounds A _ _ R.c (-t) point).2
    have first := mul_nonneg kp (show 0≤A.loU+A.side-(base+1) by
      linarith only [face,ha])
    have second := mul_nonneg hp (show 0≤(47/20)*(A.c-A.s)-A.loV by
      linarith only [m.2.2.1])
    dsimp [K,H] at first second ⊢
    nlinarith only [bound,first,second]
  rcases alternatives A R t hc an.1 rn rs narrow same p f marker top apart with au | av | ru
  · rcases low with hu | hv
    · have point := corner R R.loU R.loV
        ⟨le_rfl,by linarith only [rheight]⟩ ⟨le_rfl,by linarith only [rheight]⟩
      have bound := (closed_bounds R _ _ A.c A.s point).1
      rw [rs] at bound
      have first := mul_nonneg kp (sub_nonneg.mpr rtop.le)
      have second := mul_nonneg hp (sub_nonneg.mpr rmarker.le)
      have scalar := DiagonalOuterElbowBounds.shallow_incoming an rn narrow
      have identity :
          K*((12/5)*R.c-3*t)+H*((1543/500)*t+2*R.c)=
            2*(A.c+A.s)+A.c*(2/5+(343/500)*t^2-R.c*t)+
              A.s*(t^2+(343/500)*R.c*t) := by
        dsimp [K,H]
        linear_combination ((12/5)*A.c+2*A.s)*rn.2.2
      dsimp [K,H] at first second identity
      nlinarith only [bound,first,second,identity,scalar,au,hu,ha]
    · have base := nw hv
      have projection := (strict_bounds R _ _ A.c A.s A.unit_normal top).1
      have width : (3/4)*A.c+(13/20)*A.s<1 := by
        have square := sq_nonneg ((13/20)*A.c-(3/4)*A.s)
        have positive : 0≤(3/4)*A.c+(13/20)*A.s := by positivity
        nlinarith only [square,positive,an.2.2]
      nlinarith only [au,base,projection,width,ha]
  · have projection := (strict_bounds R _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) top).2
    nlinarith only [av,projection,p.2.2.1,hc,an.2.1]
  · rcases low with hu | hv
    · have bound := support (2*A.c+2*A.s) hu
      have scalar := DiagonalOuterElbowBounds.shallow_u an rn
      have identity :
          K*(2*A.c+2*A.s+1)-H*((47/20)*(A.c-A.s))-((12/5)*R.c-3*t)=
            R.c*(A.c-2/5+(7/20)*A.s^2-(7/20)*A.c*A.s)+
              t*(13/20-A.s+(7/20)*A.s^2+(7/20)*A.c*A.s) := by
        dsimp [K,H]
        linear_combination (2*R.c-(47/20)*t)*A.unit_normal
      linarith only [bound,ru,rtop,scalar,identity]
    · have bound := support ((33/20)*A.c+(47/20)*A.s) (nw hv)
      have scalar := DiagonalOuterElbowBounds.shallow_v an rn
      have identity :
          K*((33/20)*A.c+(47/20)*A.s+1)-H*((47/20)*(A.c-A.s))-
            ((12/5)*R.c-3*t)=R.c*(A.c-3/4+(7/10)*A.s^2)+
              t*(13/20-A.s+(7/10)*A.c*A.s) := by
        dsimp [K,H]
        linear_combination ((33/20)*R.c-(47/20)*t)*A.unit_normal
      linarith only [bound,ru,rtop,scalar,identity]

private theorem steep (A R T : OpenSquare) (t : ℝ)
    (ha : 1<A.side) (hc : 0<A.c) (an : Normal A.s A.c) (rn : Normal R.c t)
    (rs : R.s=-t) (narrow : 2*t≤R.c) (same : A.side=R.side)
    (p : A.Inside 2 (113/50)) (f : A.Inside (113/50) 3)
    (m : A.Inside (47/20) (47/20)) (missing : ¬A.Inside 2 2)
    (marker : R.Inside (1543/500) 2) (top : R.Inside (12/5) 3)
    (left : T.Inside (87/50) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y))
    (topApart : ∀ x y, ¬(A.Inside x y ∧ T.Inside x y)) : False := by
  have ab := normal_bounds an
  have rb := normal_bounds rn
  have ht := rn.1
  have hs : 0≤A.s := by linarith only [ab.1]
  have low : 2*A.c+2*A.s≤A.loU := by
    apply le_of_not_gt
    intro hu
    apply missing
    refine ⟨by linarith only [hu],?_,?_,?_⟩
    · nlinarith only [m.2.1,hc,hs]
    · nlinarith only [m.2.2.1,an.2.1]
    · nlinarith only [p.2.2.2,hc]
  have cap : A.loV+A.side≤3*A.c-(87/50)*A.s := by
    apply le_of_not_gt
    intro high
    apply topApart (87/50) 3
    refine ⟨⟨?_,?_,?_,by linarith only [high]⟩,left⟩
    · nlinarith only [m.1,hc,an.2.1]
    · nlinarith only [low,ha,ab.2.1,hc]
    · nlinarith only [f.2.2.1,hs]
  rcases alternatives A R t hc hs rn rs narrow same p f marker top apart with au | av | ru
  · have a := (strict_bounds A _ _ A.c A.s A.unit_normal f).2
    have r := (strict_bounds R _ _ A.c A.s A.unit_normal marker).1
    rw [(ownU A).2] at a
    nlinarith only [au,a,r,hc,an.2.1]
  · have r := (strict_bounds R _ _ (-A.s) A.c
      (by nlinarith only [A.unit_normal]) top).2
    nlinarith only [av,r,cap,ha,ab.2.1]
  · have height : 0≤A.side := by linarith only [ha]
    let u := (113/50)*A.c+3*A.s
    have point := corner A u A.loV
      ⟨by dsimp [u]; linarith only [f.1],by dsimp [u]; linarith only [f.2.1]⟩
      ⟨le_rfl,by linarith only [height]⟩
    have bound := (closed_bounds A _ _ R.c (-t) point).2
    have H : 0≤R.c*A.s+t*A.c := by
      have rc : 0≤R.c := by linarith only [rb.1]
      positivity
    have weight := mul_nonneg H
      (show 0≤3*A.c-(87/50)*A.s-1-A.loV by linarith only [cap,ha])
    have scalar := DiagonalOuterElbowBounds.steep an rn
    have identity :
        (R.c*A.c-t*A.s)*u-(R.c*A.s+t*A.c)*(3*A.c-(87/50)*A.s-1)-
          ((12/5)*R.c-3*t)=
        R.c*(A.s-(13/25)*A.s^2-7/50)+t*A.c*(1-(13/25)*A.s) := by
      dsimp [u]
      linear_combination ((113/50)*R.c-3*t)*A.unit_normal
    have rtop : R.loU<(12/5)*R.c-3*t := by
      have bound := top.1
      rw [rs] at bound
      linarith only [bound]
    dsimp [u] at bound identity
    nlinarith only [bound,weight,scalar,identity,rtop,ru]

/-- All orientations, with the original side cap used only to identify
the actual diagonal wall's signed frame. -/
theorem point (A R T : OpenSquare) (ha : 1<A.side)
    (same : A.side=R.side) (size : R.side≤1001/1000)
    (p : A.Inside 2 (113/50)) (f : A.Inside (113/50) 3)
    (m : A.Inside (47/20) (47/20))
    (missingNW : ¬A.Inside (33/20) (47/20))
    (marker : R.Inside (1543/500) 2)
    (right : R.Inside 3 (12/5)) (top : R.Inside (12/5) 3)
    (corner : ¬R.Inside 3 3) (left : T.Inside (87/50) 3)
    (apart : ∀ x y, ¬(A.Inside x y ∧ R.Inside x y))
    (topApart : ∀ x y, ¬(A.Inside x y ∧ T.Inside x y)) : A.Inside 2 2 := by
  obtain ⟨a,hc,hs,side,inside,_⟩ := ClosedFrames.positive_frame A
  obtain ⟨r,rc,canonical,rside,rinside,_⟩ := ClosedFrames.canonical_frame R
  have amarker := (rinside _ _).mpr marker
  have aright := (rinside _ _).mpr right
  have atop := (rinside _ _).mpr top
  have frame := DiagonalWallCenter.wall_frame r rc canonical
    (by simpa only [rside] using size) amarker aright atop
    (fun h => corner ((rinside _ _).mp h))
  let t := -r.s
  have rn : Normal r.c t := by
    refine ⟨?_,?_,?_⟩
    · dsimp [t]; linarith only [frame.1]
    · dsimp [t]; linarith only [(abs_le.mp canonical).1]
    · dsimp [t]; nlinarith only [r.unit_normal]
  have rs : r.s=-t := by dsimp [t]; ring
  have narrow : 2*t≤r.c := by dsimp [t]; linarith only [frame.2]
  have ha' : 1<a.side := by simpa only [side] using ha
  have same' : a.side=r.side := side.trans (same.trans rside.symm)
  have ap := (inside _ _).mpr p
  have af := (inside _ _).mpr f
  have am := (inside _ _).mpr m
  have ar : ∀ x y, ¬(a.Inside x y ∧ r.Inside x y) :=
    fun x y h => apart x y ⟨(inside x y).mp h.1,(rinside x y).mp h.2⟩
  by_contra failure
  have absent : ¬a.Inside 2 2 := fun h => failure ((inside _ _).mp h)
  by_cases order : a.s≤a.c
  · exact shallow a r t ha' ⟨hs,order,a.unit_normal⟩ rn rs narrow same'
      ap af am absent (fun h => missingNW ((inside _ _).mp h)) amarker atop ar
  · have normal : Normal a.s a.c := ⟨hc.le,(lt_of_not_ge order).le,
      by nlinarith only [a.unit_normal]⟩
    exact steep a r T t ha' hc normal rn rs narrow same' ap af am absent amarker atop
      left ar (fun x y h => topApart x y ⟨(inside x y).mp h.1,h.2⟩)

#print axioms point
end N12Compact.DiagonalOuterElbow
