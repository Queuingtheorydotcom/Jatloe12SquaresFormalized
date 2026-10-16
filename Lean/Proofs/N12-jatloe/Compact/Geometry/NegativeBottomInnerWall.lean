import Compact.Geometry.NegativeBottomNextWall

/-! A shallow negative bottom singleton cannot be disjoint from a
negative next wall which owns (2,1). The inner point must come from the
actual paired corner; it is not a point forced by the wall alone.
Every directed SAT axis is retained. Source only, uncompiled. -/
namespace N12Compact.NegativeBottomInnerWall

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977CornerSectorBounds C977NegativeCorner
set_option Elab.async false

/-- A negative singleton missing the southwest corner extends beyond
(2,1) in every negative canonical longitudinal direction. -/
theorem negative_projection (O : OpenSquare) (t d r : ℝ)
    (os : O.s=-t) (on : Normal O.c t) (dn : Normal d r)
    (side : 1<O.side) (corner : O.c-t≤O.loU)
    (floor : t*(O.loU+O.side)≤O.c*O.loV)
    (marker : O.Inside 1 (457/500)) :
    2*d-r<upper O d (-r) := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have cp : 0<O.c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [db.1]
  let K : ℝ := O.c*d+t*r
  let H : ℝ := t*d-O.c*r
  have kp : 0<K := by
    dsimp [K]
    exact add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg on.1 dn.1)
  by_cases order : r≤t
  · have cosine := cosine_order on dn order
    have hp : 0≤H := by
      have first := mul_nonneg on.1 (sub_nonneg.mpr cosine)
      have second := mul_nonneg cp.le (sub_nonneg.mpr order)
      dsimp [H]; nlinarith only [first,second]
    have form : upper O d (-r)=K*(O.loU+O.side)+H*(O.loV+O.side) := by
      rw [upper_in_bands,os]
      have u : d*O.c+(-r)*(-t)=K := by dsimp [K]; ring
      have v : -d*(-t)+(-r)*O.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp.le,abs_of_nonneg hp]
      ring
    have first := mul_nonneg dp.le (sub_nonneg.mpr corner)
    have second := mul_nonneg hp (sub_nonneg.mpr floor)
    have width := mul_pos (sub_pos.mpr side)
      (show 0<d+O.c*H by nlinarith only [dp,mul_nonneg cp.le hp])
    have defect := mul_nonneg (sub_nonneg.mpr ob.2.1)
      (add_nonneg (mul_nonneg dp.le (sub_nonneg.mpr ob.2.2.2.1))
        (mul_nonneg cp.le dn.1))
    have identity : O.c*(upper O d (-r)-(2*d-r))=
        d*(O.loU-(O.c-t))+H*(O.c*O.loV-t*(O.loU+O.side))+
        (O.side-1)*(d+O.c*H)+(1-O.c)*(d*(1-t)+O.c*r) := by
      rw [form]
      dsimp [K,H]
      linear_combination (d*(O.loU+O.side))*on.2.2
    have strict : 0<O.c*(upper O d (-r)-(2*d-r)) := by
      linarith only [identity,first,second,width,defect]
    have gap := pos_of_mul_pos_right strict cp.le
    linarith only [gap]
  · have order' : t≤r := le_of_not_ge order
    have cosine := cosine_order dn on order'
    have hn : H≤0 := by
      have first := mul_nonneg on.1 (sub_nonneg.mpr cosine)
      have second := mul_nonneg cp.le (sub_nonneg.mpr order')
      dsimp [H]; nlinarith only [first,second]
    have form : upper O d (-r)=K*(O.loU+O.side)+H*O.loV := by
      rw [upper_in_bands,os]
      have u : d*O.c+(-r)*(-t)=K := by dsimp [K]; ring
      have v : -d*(-t)+(-r)*O.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp.le,abs_of_nonpos hn]
      ring
    have markerV : O.loV<t+(457/500)*O.c := by
      have h := marker.2.2.1
      rw [os] at h
      nlinarith only [h]
    let M : ℝ := O.c-1-(43/500)*O.c*t
    let N : ℝ := t+(43/500)*O.c^2
    have mn : M≤0 := by
      have h := mul_nonneg cp.le on.1
      dsimp [M]; nlinarith only [ob.2.1,h]
    have np : 0≤N := by dsimp [N]; nlinarith only [on.1,sq_nonneg O.c]
    have compare₀ := mul_nonneg (neg_nonneg.mpr (sub_nonpos.mpr cosine))
      (neg_nonneg.mpr mn)
    have compare₁ := mul_nonneg (sub_nonneg.mpr order') np
    have residual : 0≤d*M+r*N := by
      have endpoint : O.c*M+t*N=1-O.c := by
        dsimp [M,N]; linear_combination on.2.2
      nlinarith only [compare₀,compare₁,endpoint,ob.2.1]
    have first := mul_nonneg kp.le (sub_nonneg.mpr corner)
    have second := mul_nonneg (neg_nonneg.mpr hn)
      (sub_nonneg.mpr markerV.le)
    have width := mul_pos (sub_pos.mpr side) kp
    have identity : upper O d (-r)-(2*d-r)=
        K*(O.loU-(O.c-t))+H*(O.loV-(t+(457/500)*O.c))+
        (O.side-1)*K+d*M+r*N := by
      rw [form]
      dsimp [K,H,M,N]
      linear_combination (d-r)*on.2.2
    clear_value K H M N
    nlinarith only [identity,first,second,width,residual]

/-- The actual northeast vertex is right of x=2 and above the wall's
marker row. Its support therefore excludes both positive transverse axes. -/
theorem positive_projection (O : OpenSquare) (t x y : ℝ)
    (os : O.s=-t) (on : Normal O.c t) (side : 1<O.side)
    (wide : 457/500<O.c) (corner : O.c-t≤O.loU)
    (floor : t*(O.loU+O.side)≤O.c*O.loV)
    (xp : 0≤x) (yp : 0<y) :
    2*x+(457/500)*y<upper O x y := by
  have ob := normal_bounds on
  have cp : 0<O.c := by linarith only [ob.1]
  let X := O.c*(O.loU+O.side)+t*(O.loV+O.side)
  let Y := -t*(O.loU+O.side)+O.c*(O.loV+O.side)
  have vertex : ClosedInside O X Y := by
    have u : O.c*X+O.s*Y=O.loU+O.side := by
      rw [os]; dsimp [X,Y]
      linear_combination (O.loU+O.side)*on.2.2
    have v : -O.s*X+O.c*Y=O.loV+O.side := by
      rw [os]; dsimp [X,Y]
      linear_combination (O.loV+O.side)*on.2.2
    change O.loU≤_ ∧ _≤O.loU+O.side ∧ O.loV≤_ ∧ _≤O.loV+O.side
    rw [u,v]
    exact ⟨by linarith only [O.side_pos],le_rfl,
      by linarith only [O.side_pos],le_rfl⟩
  have right : 2<X := by
    have first := sub_nonneg.mpr corner
    have second := mul_nonneg on.1 (sub_nonneg.mpr floor)
    have width := mul_pos (sub_pos.mpr side)
      (show 0<1+O.c*t by nlinarith only [mul_nonneg cp.le on.1])
    have defect := mul_nonneg (sub_nonneg.mpr ob.2.1)
      (sub_nonneg.mpr ob.2.2.2.1)
    have identity : O.c*(X-2)=(O.loU-(O.c-t))+
        t*(O.c*O.loV-t*(O.loU+O.side))+
        (O.side-1)*(1+O.c*t)+(1-O.c)*(1-t) := by
      dsimp [X]
      linear_combination (O.loU+O.side)*on.2.2
    have strict : 0<O.c*(X-2) := by
      linarith only [identity,first,second,width,defect]
    have gap := pos_of_mul_pos_right strict cp.le
    linarith only [gap]
  have above : 457/500<Y := by
    have width := mul_pos cp (sub_pos.mpr side)
    dsimp [Y]
    nlinarith only [floor,width,wide]
  have first := mul_nonneg xp (sub_nonneg.mpr right.le)
  have second := mul_pos yp (sub_pos.mpr above)
  have bound := (closed_bounds O X Y x y vertex).2
  clear_value X Y
  nlinarith only [first,second,bound]

/-- The actual inner point eliminates the two longitudinal SAT choices;
the true northeast vertex eliminates the two transverse choices. -/
theorem impossible_of_cosine (O D : OpenSquare) (t r : ℝ)
    (os : O.s=-t) (ds : D.s=-r)
    (on : Normal O.c t) (dn : Normal D.c r) (wide : 457/500<O.c)
    (same : O.side=D.side) (side : 1<O.side) (box : InsideContainer O)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oMiddle : O.Inside (87/50) 1) (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1)
    (dMarker : D.Inside 2 (457/500)) (inner : D.Inside 2 1)
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) : False := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dc : 0<D.c := by linarith only [db.1]
  have faces := corner_face O t os on side box oMarker oNear oFar missingCorner
  have rule (d r : ℝ) (normal : Normal d r)
      (u : upper O d (-r)≤lower D d (-r) ∨
        (43/130*d<r ∧ upper O r d≤lower D r d)) : False := by
    have bounds := normal_bounds normal
    have dp : 0<d := by linarith only [bounds.1]
    rcases u with longitudinal | transverse
    · have past := negative_projection O t d r os on normal side faces.1 faces.2.1 oMarker
      have below := (strict_bounds D 2 1 d (-r)
        (by nlinarith only [normal.2.2]) inner).1
      nlinarith only [past,below,longitudinal]
    · have past := positive_projection O t r d os on side wide faces.1 faces.2.1 normal.1 dp
      have below := (strict_bounds D 2 (457/500) r d
        (by nlinarith only [normal.2.2]) dMarker).1
      nlinarith only [past,below,transverse.2]
  have axes := C696BottomChainSelectors.singleton_wall O D oc dc
    (by rw [os]; linarith only [on.1,oc])
    (by rw [ds]; linarith only [dn.1,dc]) same oMarker oMiddle oFar dMarker apart
  rcases axes with own | next
  · apply rule O.c t on
    simpa only [C696BottomChainSelectors.SingletonStep,os,neg_neg] using own
  · apply rule D.c r dn
    simpa only [C696BottomChainSelectors.SingletonStep,ds,neg_neg] using next

/-- The convenient shallow-angle entrance implies the stronger cosine
entrance; the geometric argument itself only needs c>.914. -/
theorem impossible (O D : OpenSquare) (t r : ℝ)
    (os : O.s=-t) (ds : D.s=-r)
    (on : Normal O.c t) (dn : Normal D.c r) (small : t≤1/5)
    (same : O.side=D.side) (side : 1<O.side) (box : InsideContainer O)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oMiddle : O.Inside (87/50) 1) (oFar : O.Inside (187/100) (19/25))
    (missingCorner : ¬O.Inside 1 1)
    (dMarker : D.Inside 2 (457/500)) (inner : D.Inside 2 1)
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) : False := by
  have ob := normal_bounds on
  have wide : 457/500<O.c := by
    have bound := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤1/5+t by linarith only [on.1])
    by_contra no
    have square := mul_nonneg (show 0≤457/500-O.c by linarith only [no])
      (show 0≤457/500+O.c by linarith only [ob.1])
    nlinarith only [bound,square,on.2.2]
  exact impossible_of_cosine O D t r os ds on dn wide same side box
    oMarker oNear oMiddle oFar missingCorner dMarker inner apart

#print axioms negative_projection
#print axioms positive_projection
#print axioms impossible_of_cosine
#print axioms impossible
end N12Compact.NegativeBottomInnerWall
