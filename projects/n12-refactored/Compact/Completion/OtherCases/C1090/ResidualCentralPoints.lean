import Compact.Completion.CommonCases.CanonicalScalars
import Compact.Geometry.ClosedFrames

/-! The two all-angle transfers in C974-C976-CENTRAL-CROSSPOINTS,
Theorems 3 and 4. They are used with the actual C1090 residual owners,
but contain no family, wall, center, or angle premise. All omissions are
weak exterior conditions. This is source translation, not a replay receipt. -/
namespace N12Compact.Completion.OtherCases.C1090.ResidualCentralPoints
open S12 S12Pilot
set_option Elab.async false

private theorem short_projection (c s a b : ℝ) (unit : c^2+s^2=1)
    (short : a^2+b^2<1) : a*c+b*s<1 := by
  have identity : (a*c+b*s)^2+(a*s-b*c)^2=a^2+b^2 := by
    linear_combination (a^2+b^2)*unit
  nlinarith only [identity,short,sq_nonneg (a*s-b*c),sq_nonneg (a*c+b*s-1)]

private theorem mixed_positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (near : q.Inside 0 (13/50))
    (far : q.Inside (13/50) 1)
    (left : ¬q.Inside (-7/20) (7/20))
    (origin : ¬q.Inside 0 1) (corner : ¬q.Inside 1 1)
    (right : ¬q.Inside 1 (13/50)) : q.Inside (21/50) (4/25) := by
  have cu : q.c≤1 := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have lower : -(7/20)*q.c+(7/20)*q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply left
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [low,near.2.1,near.2.2.1,far.2.2.2,cp,sn,order]
  have upper : q.loV+q.side≤q.c := by
    apply le_of_not_gt
    intro high
    have originLower : q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      apply origin
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,high,far.2.1,marker.2.2.1,cp,sn,order]
    have cornerUpper : q.loV+q.side≤q.c-q.s := by
      apply le_of_not_gt
      intro cap
      apply corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [marker.1,marker.2.2.1,originLower,side,cu,cp,sn,order,cap]
    have rightLower : -(1:ℝ)*q.s+(13/50)*q.c≤q.loV := by
      apply le_of_not_gt
      intro low
      apply right
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [marker.1,far.2.2.2,originLower,side,cu,cp,sn,order,low]
    linarith only [cornerUpper,rightLower,side,cu]
  have short := short_projection q.c q.s (21/25) (21/50) q.unit_normal (by norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [near.1,cp,order]
  · linarith only [lower,side,cu,sn]
  · linarith only [upper,side,short]
  · linarith only [marker.2.2.2,cp,sn]

private theorem mixed_negative (q : OpenSquare) (s : ℝ) (signed : q.s=-s)
    (side : 1<q.side) (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (near : q.Inside 0 (13/50))
    (far : q.Inside (13/50) 1)
    (origin : ¬q.Inside 0 1) (corner : ¬q.Inside 1 1) :
    q.Inside (21/50) (4/25) := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu : q.c≤1 := (CommonCases.CanonicalScalars.bounds q.c s cp sn order unit).2.1
  have m := marker
  have f := near
  have g := far
  simp only [OpenSquare.Inside,InBands,signed,mul_zero,mul_one,neg_neg] at m f g
  have lower : -s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply origin
    simp only [OpenSquare.Inside,InBands,signed,mul_zero,mul_one,neg_neg]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,g.2.1,g.2.2.2,m.2.2.1,cp,sn,order]
  have upper : q.loV+q.side≤q.c+s := by
    apply le_of_not_gt
    intro high
    apply corner
    simp only [OpenSquare.Inside,InBands,signed,mul_one,neg_neg]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [m.1,m.2.2.1,lower,side,cu,cp,sn,order,high]
  have short := short_projection q.c s (21/50) (21/25) unit (by norm_num)
  have lowV : q.loV<(21/50)*s+(4/25)*q.c := by
    by_cases steep : (5/21)*q.c≤s
    · linarith only [f.2.2.1,steep]
    · have small : s≤5/21 := by linarith only [steep,cu]
      linarith only [upper,side,cu,small]
  simp only [OpenSquare.Inside,InBands,signed,neg_neg]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [f.1,cp,sn]
  · linarith only [lower,side,short]
  · linarith only [lowV]
  · linarith only [m.2.2.2,cp,order]

/-- Theorem 3: the mixed northeast owns its lower sharp point in every
orientation. In particular the northwest marker is a literal omission. -/
theorem mixed_point (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (near : q.Inside 0 (13/50))
    (far : q.Inside (13/50) 1)
    (left : ¬q.Inside (-7/20) (7/20))
    (origin : ¬q.Inside 0 1) (corner : ¬q.Inside 1 1)
    (right : ¬q.Inside 1 (13/50)) : q.Inside (21/50) (4/25) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (mixed_positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using range)
      ((same _ _).mpr marker) ((same _ _).mpr near) ((same _ _).mpr far)
      (fun h => left ((same _ _).mp h)) (fun h => origin ((same _ _).mp h))
      (fun h => corner ((same _ _).mp h)) (fun h => right ((same _ _).mp h)))
  · exact (same _ _).mp (mixed_negative r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)
      ((same _ _).mpr marker) ((same _ _).mpr near) ((same _ _).mpr far)
      (fun h => origin ((same _ _).mp h)) (fun h => corner ((same _ _).mp h)))

structure Parameters (a b : ℝ) : Prop where
  aLow : 2/5≤a
  aHigh : a≤11/20
  bLow : 1/10≤b
  bHigh : b≤1/5
  difference : 13/50+b≤a
  sum : a+b≤37/50

private theorem southeast_positive (q : OpenSquare) (a b : ℝ) (p : Parameters a b)
    (side : 1<q.side) (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (-7/20)) (near : q.Inside (13/50) 0)
    (far : q.Inside 1 (-13/50)) (missing : ¬q.Inside a b) :
    q.Inside 1 (-1/2) := by
  have aLow := mul_le_mul_of_nonneg_right p.aLow cp.le
  have aHigh := mul_le_mul_of_nonneg_right p.aHigh sn
  have bLow := mul_le_mul_of_nonneg_right p.bLow cp.le
  have bNonnegative : 0≤b := by linarith only [p.bLow]
  have upperIncrement := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤13/50+b by linarith only [p.bLow])
  have sum := mul_nonneg cp.le (sub_nonneg.mpr p.sum)
  have lowerIncrement := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤a-7/20 by linarith only [p.aLow])
  have upper : q.loV+q.side≤ -q.s*a+q.c*b := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [near.1,aLow,cp,mul_nonneg sn bNonnegative]
    · nlinarith only [far.2.1,upperIncrement,sum]
    · have margin := mul_le_mul_of_nonneg_left
        (show 1/4≤7/10+b-a by linarith only [p.aHigh,p.bLow])
        cp.le
      nlinarith only [marker.2.2.1,lowerIncrement,margin,cp]
    · exact high
  have short := short_projection q.c q.s (7/10) (3/5) q.unit_normal (by norm_num)
  have gapA := mul_le_mul_of_nonneg_right p.aLow sn
  have gapB := mul_le_mul_of_nonneg_right p.bHigh cp.le
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [marker.1,cp,order]
  · linarith only [far.2.1,sn]
  · nlinarith only [upper,side,short,gapA,gapB]
  · linarith only [far.2.2.2,cp]

private theorem southeast_negative (q : OpenSquare) (s a b : ℝ)
    (signed : q.s=-s) (p : Parameters a b)
    (side : 1<q.side) (cp : 0<q.c) (sn : 0≤s) (order : s≤q.c)
    (marker : q.Inside (7/20) (-7/20)) (near : q.Inside (13/50) 0)
    (far : q.Inside 1 (-13/50))
    (below : ¬q.Inside 0 (-1/2)) (missing : ¬q.Inside a b) :
    q.Inside 1 (-1/2) := by
  have unit : q.c^2+s^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have cu : q.c≤1 := (CommonCases.CanonicalScalars.bounds q.c s cp sn order unit).2.1
  have m := marker
  have d := near
  have f := far
  simp only [OpenSquare.Inside,InBands,signed,mul_zero,mul_one,neg_neg] at m d f
  have lowerIncrement := mul_nonneg (sub_nonneg.mpr order)
    (show 0≤b by linarith only [p.bLow])
  have difference := mul_nonneg cp.le (sub_nonneg.mpr p.difference)
  have aLow := mul_le_mul_of_nonneg_right p.aLow sn
  have bLow := mul_le_mul_of_nonneg_right p.bLow cp.le
  have aHigh := mul_le_mul_of_nonneg_right p.aHigh cp.le
  have bNonnegative := mul_nonneg sn (show 0≤13/50+b by linarith only [p.bLow])
  have upper : q.loV+q.side≤s*a+q.c*b := by
    apply le_of_not_gt
    intro high
    apply missing
    simp only [OpenSquare.Inside,InBands,signed,neg_neg]
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [d.1,lowerIncrement,difference]
    · nlinarith only [f.2.1,aHigh,bNonnegative,cp]
    · nlinarith only [d.2.2.1,aLow,bLow,cp,sn]
    · exact high
  have short := short_projection q.c s (7/10) (11/20) unit (by norm_num)
  have capA := mul_le_mul_of_nonneg_right p.aHigh sn
  have capB := mul_le_mul_of_nonneg_right p.bHigh cp.le
  have lower : (1/2)*s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply below
    simp only [OpenSquare.Inside,InBands,signed,mul_zero,neg_neg]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [low]
    · linarith only [f.2.1,cp,order]
    · nlinarith only [upper,side,short,capA,capB]
    · linarith only [d.2.2.2,cp,sn]
  have aOne := mul_nonneg sn (show 0≤1-a by linarith only [p.aHigh])
  simp only [OpenSquare.Inside,InBands,signed,mul_one,neg_neg]
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [m.1,cp,sn]
  · linarith only [lower,side,cu]
  · nlinarith only [upper,side,capB,aOne,cu]
  · linarith only [f.2.2.2,cp]

/-- Theorem 4, including the equality a=13/50+b. No right-wall origin
is needed: the omitted sharp point and actual southwest halfpoint suffice. -/
theorem southeast_point (q : OpenSquare) (a b : ℝ) (p : Parameters a b)
    (side : 1<q.side)
    (marker : q.Inside (7/20) (-7/20)) (near : q.Inside (13/50) 0)
    (far : q.Inside 1 (-13/50))
    (below : ¬q.Inside 0 (-1/2)) (missing : ¬q.Inside a b) :
    q.Inside 1 (-1/2) := by
  obtain ⟨r,cp,range,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  by_cases sign : 0≤r.s
  · exact (same _ _).mp (southeast_positive r a b p side' cp sign
      (by simpa only [abs_of_nonneg sign] using range)
      ((same _ _).mpr marker) ((same _ _).mpr near) ((same _ _).mpr far)
      (fun h => missing ((same _ _).mp h)))
  · exact (same _ _).mp (southeast_negative r (-r.s) a b (by ring) p side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using range)
      ((same _ _).mpr marker) ((same _ _).mpr near) ((same _ _).mpr far)
      (fun h => below ((same _ _).mp h)) (fun h => missing ((same _ _).mp h)))

#print axioms mixed_point
#print axioms southeast_point
end N12Compact.Completion.OtherCases.C1090.ResidualCentralPoints
