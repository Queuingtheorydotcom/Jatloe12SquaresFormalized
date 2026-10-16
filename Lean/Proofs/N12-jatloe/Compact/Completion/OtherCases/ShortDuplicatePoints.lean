import Compact.Completion.OtherCases.OutwardBarPoint
import Compact.Geometry.ClosedFrames
import S12.ShortCluster
import S12.Convex

/-! The full inward Theorem 2 of C974-C976-DUPLICATE-POINT, together
with a shorter outward corollary for applications with an actual whole bar.
The outward corollary uses a rational triangle in the already proved sharp
bar point; it does not claim the isolated-exclusion version of Theorem 1.
All conclusions are strict and all omitted points may touch the boundary.
Written source only; no compilation has been run. -/
namespace N12Compact.Completion.OtherCases.ShortDuplicatePoints
open S12 S12Pilot
set_option Elab.async false

theorem inward_positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (inward : q.Inside 0 (13/50))
    (elbow : q.Inside (13/50) 0) (top : q.Inside (2/5) 1)
    (missingF : ¬q.Inside (13/50) 1)
    (missingL : ¬q.Inside (-7/20) (7/20))
    (missingB : ¬q.Inside (7/20) (-7/20)) :
    q.Inside (1/2) (1/25) := by
  have lowerU : q.loU<q.c/2+q.s/25 := by linarith only [elbow.1,cp,sn]
  have upperV : -q.s/2+q.c/25<q.loV+q.side := by
    linarith only [marker.2.2.2,cp,sn]
  have cu := (CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  by_cases steep : q.c≤6*q.s
  · have fLowerU : q.loU<(13/50)*q.c+q.s := by
      linarith only [marker.1,steep,cp]
    have fUpperU : (13/50)*q.c+q.s<q.loU+q.side := by
      linarith only [top.2.1,cp]
    have fLowerV : q.loV< -(13/50)*q.s+q.c := by
      linarith only [marker.2.2.1,cp,sn]
    have fUpperV : q.loV+q.side≤ -(13/50)*q.s+q.c := by
      apply le_of_not_gt
      intro high
      apply missingF
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [fLowerU,fUpperU,fLowerV,high]
    have short := (short_projections q (-6/25) (24/25) (by norm_num)).2.2.2
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [lowerU]
    · linarith only [top.2.1,steep,cp]
    · linarith only [fUpperV,short,side]
    · linarith only [upperV]
  · have shallow : 6*q.s<q.c := lt_of_not_ge steep
    have lowerV : q.loV< -q.s/2+q.c/25 := by
      linarith only [elbow.2.2.1,shallow]
    have bLowerU : q.loU<(7/20)*q.c-(7/20)*q.s := by
      linarith only [elbow.1,shallow,cp]
    have bUpperU : (7/20)*q.c-(7/20)*q.s<q.loU+q.side := by
      linarith only [marker.2.1,sn]
    have bUpperV : -(7/20)*q.s-(7/20)*q.c<q.loV+q.side := by
      linarith only [elbow.2.2.2,cp,sn]
    have bLowerV : -(7/20)*q.s-(7/20)*q.c≤q.loV := by
      apply le_of_not_gt
      intro low
      apply missingB
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [bLowerU,bUpperU,low,bUpperV]
    have lUpperU : -(7/20)*q.c+(7/20)*q.s<q.loU+q.side := by
      linarith only [inward.2.1,cp,order]
    have lLowerV : q.loV<(7/20)*q.s+(7/20)*q.c := by
      linarith only [inward.2.2.1,cp,sn]
    have lUpperV : (7/20)*q.s+(7/20)*q.c<q.loV+q.side := by
      linarith only [bLowerV,side,shallow,cu]
    have lLowerU : -(7/20)*q.c+(7/20)*q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      apply missingL
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,lUpperU,lLowerV,lUpperV]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lowerU,lowerV,upperV,lLowerU,side,cu,sn]

theorem inward_negative (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : q.s≤0) (order : -q.s≤q.c)
    (marker : q.Inside (7/20) (7/20)) (inward : q.Inside 0 (13/50))
    (elbow : q.Inside (13/50) 0) (top : q.Inside (2/5) 1)
    (missingF : ¬q.Inside (13/50) 1) : q.Inside (1/2) (1/25) := by
  have lowerU : q.loU<q.c/2+q.s/25 := by linarith only [elbow.1,cp,order]
  have lowerV : q.loV< -q.s/2+q.c/25 := by linarith only [elbow.2.2.1,cp,sn]
  have upperV : -q.s/2+q.c/25<q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have fUpperU : (13/50)*q.c+q.s<q.loU+q.side := by
    linarith only [top.2.1,cp]
  have fLowerV : q.loV< -(13/50)*q.s+q.c := by
    linarith only [inward.2.2.1,cp,sn]
  have fUpperV : -(13/50)*q.s+q.c<q.loV+q.side := by
    linarith only [top.2.2.2,sn]
  have fLowerU : (13/50)*q.c+q.s≤q.loU := by
    apply le_of_not_gt
    intro low
    apply missingF
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,fUpperU,fLowerV,fUpperV]
  have short := (short_projections q (6/25) (-24/25) (by norm_num)).2.1
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lowerU,lowerV,upperV,fLowerU,side,short]

theorem inward (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (7/20) (7/20)) (inward : q.Inside 0 (13/50))
    (elbow : q.Inside (13/50) 0) (top : q.Inside (2/5) 1)
    (missingF : ¬q.Inside (13/50) 1)
    (missingL : ¬q.Inside (-7/20) (7/20))
    (missingB : ¬q.Inside (7/20) (-7/20)) : q.Inside (1/2) (1/25) := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have sideR : 1<r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr inward
  have d := (same _ _).mpr elbow
  have t := (same _ _).mpr top
  have f : ¬r.Inside (13/50) 1 := fun own => missingF ((same _ _).mp own)
  apply (same _ _).mp
  by_cases sign : 0≤r.s
  · exact inward_positive r sideR cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m a d t f
      (fun own => missingL ((same _ _).mp own))
      (fun own => missingB ((same _ _).mp own))
  · exact inward_negative r sideR cp (le_of_not_ge sign)
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) m a d t f

theorem inward_original (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20)) (inwardPoint : q.Inside 2 (113/50))
    (elbow : q.Inside (113/50) 2) (top : q.Inside (12/5) 3)
    (missingF : ¬q.Inside (113/50) 3)
    (missingL : ¬q.Inside (33/20) (47/20))
    (missingB : ¬q.Inside (47/20) (33/20)) : q.Inside (5/2) (51/25) := by
  have result := inward (q.translated 2 2) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact inwardPoint)
    (by norm_num [inside_translated_iff]; exact elbow)
    (by norm_num [inside_translated_iff]; exact top)
    (by norm_num [inside_translated_iff]; exact missingF)
    (by norm_num [inside_translated_iff]; exact missingL)
    (by norm_num [inside_translated_iff]; exact missingB)
  norm_num [inside_translated_iff] at result
  exact result

/-- This specific strict point lies in a rational triangle of the actual
marker, outward anchor and sharper bar point. No optimization is repeated. -/
theorem outward_of_bar (q : OpenSquare) (side : 1<q.side)
    (marker : q.Inside (47/20) (47/20))
    (outward : q.Inside 3 (113/50)) (upper : q.Inside 3 (12/5))
    (missingG : ¬q.Inside (113/50) 2) (missingR : ¬q.Inside (1543/500) 2)
    (missingP : ¬q.Inside 3 3) (missingH : ¬q.Inside (1543/500) 3)
    (avoid : ∀ z : ℝ,113/50≤z → z≤14/5 → ¬q.Inside z 3) :
    q.Inside (5/2) (49/25) := by
  have sharp := OutwardBarPoint.point_original q side marker outward upper
    missingG missingR missingP missingH avoid
  let cert : TriangleCertificate :=
    ⟨(47/20,47/20),(3,113/50),(101/40,15/8),(5/2,49/25),3/53,240/293⟩
  have checked : cert.Check := by decide +kernel
  have result := triangle_certificate_sound cert checked q
    (by norm_num [cert]; exact marker)
    (by norm_num [cert]; exact outward)
    (by norm_num [cert]; exact sharp)
  norm_num [cert] at result
  exact result

#print axioms inward_original
#print axioms outward_of_bar
end N12Compact.Completion.OtherCases.ShortDuplicatePoints
