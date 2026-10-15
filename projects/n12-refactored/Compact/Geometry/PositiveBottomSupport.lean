import Compact.Geometry.PositiveBottomNextAxes

/-! The genuine bottom containment and missing-corner face give a
uniform positive-direction support. No sampled orientation or virtual
axis wall replaces the actual square. -/
namespace N12Compact.PositiveBottomSupport

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

theorem positive_projection (O : OpenSquare) {d r : ℝ}
    (on : Normal O.c O.s) (dn : Normal d r) (side : 1<O.side)
    (cap : O.loV+O.side≤O.c-O.s)
    (floor : 0≤O.s*O.loU+O.c*O.loV) :
    2*d+r/2<upper O d r := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have oc : 0<O.c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [db.1]
  let K := d*O.c+r*O.s
  let H := r*O.c-d*O.s
  have kp : 0<K := by
    have first := mul_pos dp oc
    have last := mul_nonneg dn.1 on.1
    dsimp [K]; nlinarith only [first,last]
  have defect : 0≤1-O.c := sub_nonneg.mpr ob.2.1
  have chord : 0≤O.s-(1-O.c)/2 := by
    linarith only [ob.2.2.2.2.1,on.1]
  have endpoint := mul_nonneg dp.le (mul_nonneg defect chord)
  have floorWeight := mul_nonneg kp.le floor
  have capWeight := mul_nonneg dp.le (sub_nonneg.mpr cap)
  by_cases hp : 0≤H
  · have formula : upper O d r=K*(O.loU+O.side)+H*(O.loV+O.side) := by
      rw [upper_in_bands]
      have u : d*O.c+r*O.s=K := rfl
      have v : -d*O.s+r*O.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp.le,abs_of_nonneg hp]; ring
    let R := -d*(1-O.c)*(O.c+O.s)+r*O.s*(O.c+O.s-1/2)
    have weight := mul_nonneg hp
      (mul_nonneg on.1 (show 0≤O.c+O.s-1/2 by linarith only [ob.2.2.2.2.1]))
    have residual : O.c*R=d*(1-O.c)*(O.s-(1-O.c)/2)+
        H*O.s*(O.c+O.s-1/2) := by
      dsimp [R,H]
      linear_combination d*(O.c+O.s-1/2)*on.2.2
    have nonnegative : 0≤R := by
      have scaled : 0≤O.c*R := by nlinarith only [residual,endpoint,weight]
      exact nonneg_of_mul_nonneg_right scaled oc
    have width := mul_pos (sub_pos.mpr side)
      (mul_pos kp (show 0<O.c+O.s by linarith only [ob.2.2.2.2.1]))
    have identity : O.s*(upper O d r-(2*d+r/2))=
        K*(O.s*O.loU+O.c*O.loV)+d*(O.c-O.s-(O.loV+O.side))+
        (O.side-1)*K*(O.c+O.s)+R := by
      rw [formula]
      dsimp [K,H,R]
      linear_combination (-d*(O.loV+O.side))*on.2.2
    have strict : 0<O.s*(upper O d r-(2*d+r/2)) := by
      nlinarith only [identity,floorWeight,capWeight,width,nonnegative]
    have gap := pos_of_mul_pos_right strict on.1
    linarith only [gap]
  · have hn : H≤0 := le_of_lt (lt_of_not_ge hp)
    have formula : upper O d r=K*(O.loU+O.side)+H*O.loV := by
      rw [upper_in_bands]
      have u : d*O.c+r*O.s=K := rfl
      have v : -d*O.s+r*O.c=H := by dsimp [H]; ring
      rw [u,v,abs_of_nonneg kp.le,abs_of_nonpos hn]; ring
    let R := d*(1-O.c)*(1-O.s)+r*O.s*(O.s-1/2)
    have nonnegative : 0≤R := by
      by_cases half : 1/2≤O.s
      · have first := mul_nonneg dp.le
          (mul_nonneg defect (sub_nonneg.mpr ob.2.2.2.1))
        have last := mul_nonneg (mul_nonneg dn.1 on.1) (sub_nonneg.mpr half)
        dsimp [R]; nlinarith only [first,last]
      · have weight := mul_nonneg (neg_nonneg.mpr hn)
          (mul_nonneg on.1 (show 0≤1/2-O.s by linarith only [half]))
        have residual : O.c*R=d*(1-O.c)*(O.s-(1-O.c)/2)+
            H*O.s*(O.s-1/2) := by
          dsimp [R,H]
          linear_combination d*(O.s-1/2)*on.2.2
        have scaled : 0≤O.c*R := by nlinarith only [residual,endpoint,weight]
        exact nonneg_of_mul_nonneg_right scaled oc
    have width := mul_pos (sub_pos.mpr side)
      (show 0<d+O.s*K by nlinarith only [dp,mul_nonneg on.1 kp.le])
    have identity : O.s*(upper O d r-(2*d+r/2))=
        K*(O.s*O.loU+O.c*O.loV)+d*(O.c-O.s-(O.loV+O.side))+
        (O.side-1)*(d+O.s*K)+R := by
      rw [formula]
      dsimp [K,H,R]
      linear_combination (-d*O.loV)*on.2.2
    have strict : 0<O.s*(upper O d r-(2*d+r/2)) := by
      nlinarith only [identity,floorWeight,capWeight,width,nonnegative]
    have gap := pos_of_mul_pos_right strict on.1
    linarith only [gap]

theorem own_axis (O : OpenSquare) (on : Normal O.c O.s) (side : 1<O.side)
    (cap : O.loV+O.side≤O.c-O.s)
    (floor : 0≤O.s*O.loU+O.c*O.loV) :
    2*O.c+O.s/2<O.loU+O.side := by
  simpa only [(ownU O).2] using positive_projection O on on side cap floor

/-- The same positive-direction entrance holds throughout the negative
singleton arc. The true lower corner face and bottom containment replace
the positive singleton's upper transverse face. -/
theorem negative_frame_projection (O : OpenSquare) (t : ℝ) {d r : ℝ}
    (signed : O.s=-t) (on : Normal O.c t) (dn : Normal d r)
    (side : 1<O.side) (corner : O.c-t≤O.loU)
    (floor : t*(O.loU+O.side)≤O.c*O.loV) :
    2*d+r/2<upper O d r := by
  have ob := normal_bounds on
  have db := normal_bounds dn
  have cp : 0<O.c := by linarith only [ob.1]
  have dp : 0<d := by linarith only [db.1]
  let K := d*O.c-r*t
  let H := d*t+r*O.c
  have kp : 0≤K := by
    have first := mul_nonneg cp.le (sub_nonneg.mpr dn.2.1)
    have last := mul_nonneg dn.1 (sub_nonneg.mpr on.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg dp.le on.1) (mul_nonneg dn.1 cp.le)
  have formula : upper O d r=K*(O.loU+O.side)+H*(O.loV+O.side) := by
    exact upper_negative_pos O t d r signed kp hp
  have cornerWeight := mul_nonneg dp.le (sub_nonneg.mpr corner)
  have floorWeight := mul_nonneg hp (sub_nonneg.mpr floor)
  have width := mul_pos (sub_pos.mpr side)
    (show 0<d+O.c*H by nlinarith only [dp,mul_nonneg cp.le hp])
  have first := mul_nonneg dp.le
    (mul_nonneg (sub_nonneg.mpr ob.2.1) (sub_nonneg.mpr ob.2.2.2.1))
  have last := mul_nonneg (mul_nonneg dn.1 cp.le)
    (show 0≤O.c-1/2 by linarith only [ob.1])
  have identity : O.c*(upper O d r-(2*d+r/2))=
      d*(O.loU-(O.c-t))+H*(O.c*O.loV-t*(O.loU+O.side))+
      (O.side-1)*(d+O.c*H)+d*(1-O.c)*(1-t)+r*O.c*(O.c-1/2) := by
    rw [formula]
    dsimp [K,H]
    linear_combination d*(O.loU+O.side)*on.2.2
  have strict : 0<O.c*(upper O d r-(2*d+r/2)) := by
    nlinarith only [identity,cornerWeight,floorWeight,width,first,last]
  have gap := pos_of_mul_pos_right strict cp.le
  linarith only [gap]

#print axioms positive_projection
#print axioms own_axis
#print axioms negative_frame_projection
end N12Compact.PositiveBottomSupport
