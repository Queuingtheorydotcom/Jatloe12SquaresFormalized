import Compact.Geometry.C696PositiveCorner

/-! Actual positive bottom singletons extend past the inner bottom-wall
point in every negative canonical longitudinal direction. Together with
the original anchors this retains only the directed axes which can take
part in the full bottom-wall/central support cycle. -/
namespace N12Compact.PositiveBottomNextAxes

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner C977ChainBridge
set_option Elab.async false

theorem negative_projection (O : OpenSquare) {d r : ℝ}
    (on : Normal O.c O.s) (dn : Normal d r) (side : 1<O.side)
    (tilt : 0<O.s) (cap : O.loV+O.side≤O.c-O.s)
    (floor : 0≤O.s*O.loU+O.c*O.loV) :
    2*d-r<upper O d (-r) := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0≤O.c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [db.1]
  let K := d*O.c-r*O.s
  let H := d*O.s+r*O.c
  have kp : 0≤K := by
    have first := mul_nonneg oc (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg dn.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg dp.le on.1) (mul_nonneg dn.1 oc)
  have form : upper O d (-r)=K*(O.loU+O.side)-H*O.loV := by
    rw [upper_in_bands]
    have u : d*O.c+(-r)*O.s=K := by dsimp [K]; ring
    have v : -d*O.s+(-r)*O.c=-H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonpos (neg_nonpos.mpr hp)]
    ring
  have first := mul_nonneg kp floor
  have last := mul_nonneg dp.le (sub_nonneg.mpr cap)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<d+O.s*K by nlinarith only [dp,mul_nonneg on.1 kp])
  have defect := mul_nonneg (sub_nonneg.mpr ob.2.2.2.1)
    (add_nonneg (mul_nonneg dp.le (sub_nonneg.mpr ob.2.1))
      (mul_nonneg dn.1 on.1))
  have identity : O.s*(upper O d (-r)-(2*d-r))=
      K*(O.s*O.loU+O.c*O.loV)+d*(O.c-O.s-(O.loV+O.side))+
      (O.side-1)*(d+O.s*K)+(1-O.s)*(d*(1-O.c)+r*O.s) := by
    rw [form]
    dsimp [K,H]
    linear_combination -d*O.loV*on.2.2
  have strict : 0<O.s*(upper O d (-r)-(2*d-r)) := by
    linarith only [identity,first,last,width,defect]
  have gap := pos_of_mul_pos_right strict on.1
  linarith only [gap]

/-- For a positive next wall, only the two forward longitudinal axes
remain. No saved pose enclosure or wall-angle order is assumed. -/
theorem positive_wall (O D : OpenSquare)
    (on : Normal O.c O.s) (dn : Normal D.c D.s)
    (same : O.side=D.side) (side : 1<O.side)
    (cap : O.loV+O.side≤O.c-O.s)
    (oMarker : O.Inside 1 (457/500)) (oNear : O.Inside (28/25) 1)
    (oFar : O.Inside (187/100) (19/25))
    (dMarker : D.Inside 2 (457/500))
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) :
    O.loU+O.side≤lower D O.c O.s ∨ upper O D.c D.s≤D.loU := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dc : 0<D.c := by linarith only [db.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint O D same apart
  change pairRadius O D≤|O.c*(centerX D-centerX O)+O.s*(centerY D-centerY O)| ∨
    pairRadius O D≤|-O.s*(centerX D-centerX O)+O.c*(centerY D-centerY O)| ∨
    pairRadius D O≤|D.c*(centerX D-centerX O)+D.s*(centerY D-centerY O)| ∨
    pairRadius D O≤|-D.s*(centerX D-centerX O)+D.c*(centerY D-centerY O)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius O x y+supportRadius D x y=R)
      (sep : R≤|x*(centerX D-centerX O)+y*(centerY D-centerY O)|) :=
    separated O D x y (by rwa [identity])
  rcases axes with ou | ov | du | dv
  · rcases separateAxis _ _ _ (parallel_radius O D) ou with forward | reverse
    · exact Or.inl (by simpa only [(ownU O).2] using forward)
    · have om := strict_bounds O _ _ O.c O.s O.unit_normal oMarker
      have dm := strict_bounds D _ _ O.c O.s O.unit_normal dMarker
      exfalso
      nlinarith only [reverse,om.1,dm.2,oc]
  · rcases separateAxis _ _ _ (transverse_radius O D) ov with forward | reverse
    · have om := strict_bounds O _ _ (-O.s) O.c
        (by nlinarith only [O.unit_normal]) oMarker
      have dm := strict_bounds D _ _ (-O.s) O.c
        (by nlinarith only [O.unit_normal]) dMarker
      exfalso
      nlinarith only [forward,om.2,dm.1,on.1]
    · have dm := strict_bounds D _ _ (-O.s) O.c
        (by nlinarith only [O.unit_normal]) dMarker
      rw [(ownV O).1] at reverse
      have sine : O.s≤5/7 := by linarith only [on.2.1,ob.2.2.2.2.2]
      exfalso
      nlinarith only [reverse,dm.2,cap,side,ob.2.1,sine]
  · have identity : supportRadius O D.c D.s+supportRadius D D.c D.s=pairRadius D O := by
      rw [add_comm]; exact parallel_radius D O
    rcases separateAxis _ _ _ identity du with forward | reverse
    · exact Or.inr (by simpa only [(ownU D).1] using forward)
    · have om := strict_bounds O _ _ D.c D.s D.unit_normal oMarker
      have dm := strict_bounds D _ _ D.c D.s D.unit_normal dMarker
      exfalso
      nlinarith only [reverse,om.1,dm.2,dc]
  · have identity : supportRadius O (-D.s) D.c+supportRadius D (-D.s) D.c=pairRadius D O := by
      rw [add_comm]; exact transverse_radius D O
    rcases separateAxis _ _ _ identity dv with forward | reverse
    · have om := strict_bounds O _ _ (-D.s) D.c
        (by nlinarith only [D.unit_normal]) oNear
      have dm := strict_bounds D _ _ (-D.s) D.c
        (by nlinarith only [D.unit_normal]) dMarker
      exfalso
      nlinarith only [forward,om.2,dm.1,dn.1,dc]
    · have om := strict_bounds O _ _ (-D.s) D.c
        (by nlinarith only [D.unit_normal]) oFar
      have dm := strict_bounds D _ _ (-D.s) D.c
        (by nlinarith only [D.unit_normal]) dMarker
      exfalso
      nlinarith only [reverse,om.1,dm.2,dn.2.1,dc]

/-- The actual inner wall point removes its longitudinal axis when the
wall has a negative canonical frame. Its upward transverse alternative
is retained together with the singleton's forward longitudinal one. -/
theorem negative_wall (O D : OpenSquare) (r : ℝ) (ds : D.s=-r)
    (on : Normal O.c O.s) (dn : Normal D.c r)
    (same : O.side=D.side) (side : 1<O.side) (tilt : 0<O.s)
    (cap : O.loV+O.side≤O.c-O.s)
    (floor : 0≤O.s*O.loU+O.c*O.loV)
    (oMarker : O.Inside 1 (457/500)) (oFar : O.Inside (187/100) (19/25))
    (dMarker : D.Inside 2 (457/500)) (inner : D.Inside 2 1)
    (apart : ∀ x y, ¬(O.Inside x y ∧ D.Inside x y)) :
    O.loU+O.side≤lower D O.c O.s ∨ upper O r D.c≤D.loV := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dc : 0<D.c := by linarith only [db.1]
  have axes := CongruentSAT.faceSeparation_of_disjoint O D same apart
  change pairRadius O D≤|O.c*(centerX D-centerX O)+O.s*(centerY D-centerY O)| ∨
    pairRadius O D≤|-O.s*(centerX D-centerX O)+O.c*(centerY D-centerY O)| ∨
    pairRadius D O≤|D.c*(centerX D-centerX O)+D.s*(centerY D-centerY O)| ∨
    pairRadius D O≤|-D.s*(centerX D-centerX O)+D.c*(centerY D-centerY O)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius O x y+supportRadius D x y=R)
      (sep : R≤|x*(centerX D-centerX O)+y*(centerY D-centerY O)|) :=
    separated O D x y (by rwa [identity])
  rcases axes with ou | ov | du | dv
  · rcases separateAxis _ _ _ (parallel_radius O D) ou with forward | reverse
    · exact Or.inl (by simpa only [(ownU O).2] using forward)
    · have om := strict_bounds O _ _ O.c O.s O.unit_normal oMarker
      have dm := strict_bounds D _ _ O.c O.s O.unit_normal dMarker
      exfalso
      nlinarith only [reverse,om.1,dm.2,oc]
  · rcases separateAxis _ _ _ (transverse_radius O D) ov with forward | reverse
    · have om := strict_bounds O _ _ (-O.s) O.c
        (by nlinarith only [O.unit_normal]) oMarker
      have dm := strict_bounds D _ _ (-O.s) O.c
        (by nlinarith only [O.unit_normal]) dMarker
      exfalso
      nlinarith only [forward,om.2,dm.1,on.1]
    · have dm := strict_bounds D _ _ (-O.s) O.c
        (by nlinarith only [O.unit_normal]) dMarker
      rw [(ownV O).1] at reverse
      have sine : O.s≤5/7 := by linarith only [on.2.1,ob.2.2.2.2.2]
      exfalso
      nlinarith only [reverse,dm.2,cap,side,ob.2.1,sine]
  · have identity : supportRadius O D.c D.s+supportRadius D D.c D.s=pairRadius D O := by
      rw [add_comm]; exact parallel_radius D O
    rcases separateAxis _ _ _ identity du with forward | reverse
    · have past := negative_projection O on dn side tilt cap floor
      have before := (strict_bounds D _ _ D.c (-r)
        (by nlinarith only [dn.2.2]) inner).1
      rw [ds] at forward
      exact False.elim (by linarith only [past,before,forward])
    · have om := strict_bounds O _ _ D.c D.s D.unit_normal oMarker
      have dm := strict_bounds D _ _ D.c D.s D.unit_normal dMarker
      exfalso
      nlinarith only [reverse,om.1,dm.2,dc]
  · have identity : supportRadius O (-D.s) D.c+supportRadius D (-D.s) D.c=pairRadius D O := by
      rw [add_comm]; exact transverse_radius D O
    rcases separateAxis _ _ _ identity dv with forward | reverse
    · have own : lower D r D.c = D.loV := by
        simpa only [ds, neg_neg] using (ownV D).1
      exact Or.inr (by simpa only [ds, neg_neg, own] using forward)
    · have om := strict_bounds O _ _ r D.c
        (by nlinarith only [dn.2.2]) oFar
      have dm := strict_bounds D _ _ r D.c
        (by nlinarith only [dn.2.2]) dMarker
      rw [ds,neg_neg] at reverse
      exact False.elim (by nlinarith only [reverse,om.1,dm.2,dn.1,dc])

end N12Compact.PositiveBottomNextAxes
