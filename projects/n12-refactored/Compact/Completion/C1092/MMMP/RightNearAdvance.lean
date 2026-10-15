import Compact.Geometry.ClosedFrames
import Compact.Geometry.C977CornerCubic

/-! An inward right-wall point and the genuine compulsory near endpoint
force the ordinary endpoint itself. This avoids enumerating a combined
component table in the original MMMP right-inner contradiction. -/
namespace N12Compact.C1092MMMPRightNearAdvance
open S12 S12Pilot C977CornerCubic
set_option Elab.async false

private theorem positive_impossible (q : OpenSquare) (cn : Normal q.c q.s)
    (side : 1<q.side) (A : q.Inside (13/50) 0) (S : q.Inside (543/500) 0)
    (F : ¬q.Inside 1 (-13/50)) (M : ¬q.Inside (7/20) (7/20)) : False := by
  have cb := normal_bounds cn
  have cp : 0<q.c := by linarith only [cb.1]
  have lower : -q.s-(13/50)*q.c≤q.loV := by
    apply le_of_not_gt
    intro failure
    apply F
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,A.1,S.2.1,A.2.2.2,cp,cn.1,cn.2.1]
  have upper : q.loV+q.side≤(7/20)*(q.c-q.s) := by
    apply le_of_not_gt
    intro failure
    apply M
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,A.1,S.2.1,A.2.2.1,cp,cn.1,cn.2.1]
  have short : (61/100)*q.c+(13/20)*q.s<1 := by
    nlinarith only [cn.2.2,sq_nonneg ((13/20)*q.c-(61/100)*q.s),
      sq_nonneg ((61/100)*q.c+(13/20)*q.s-1)]
  linarith only [lower,upper,side,short]

private theorem negative_point (q : OpenSquare) (cn : Normal q.c (-q.s))
    (side : 1<q.side) (A : q.Inside (13/50) 0) (S : q.Inside (543/500) 0)
    (D : q.Inside 1 (39/100))
    (F : ¬q.Inside 1 (-13/50)) (M : ¬q.Inside (7/20) (7/20)) : q.Inside 1 (2/5) := by
  have cb := normal_bounds cn
  have cp : 0<q.c := by linarith only [cb.1]
  have lowerU : (7/20)*(q.c+q.s)≤q.loU := by
    apply le_of_not_gt
    intro failure
    apply M
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,S.2.1,A.2.2.1,D.2.2.2,cp,cn.1,cn.2.1]
  have short : (13/20)*q.c+(61/100)*(-q.s)<1 := by
    nlinarith only [cn.2.2,sq_nonneg ((61/100)*q.c-(13/20)*(-q.s)),
      sq_nonneg ((13/20)*q.c+(61/100)*(-q.s)-1)]
  have lowerV : -q.s-(13/50)*q.c≤q.loV := by
    apply le_of_not_gt
    intro failure
    have upperU : q.c-(13/50)*q.s<q.loU+q.side := by linarith only [lowerU,short,side]
    apply F
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [failure,upperU,A.1,D.2.2.2,cp,cn.1,cn.2.1]
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [A.1,S.2.1,D.2.2.1,lowerV,side,cp,cn.1,cn.2.1,cb.2.1]

theorem point (q : OpenSquare) (side : 1<q.side)
    (A : q.Inside (13/50) 0) (S : q.Inside (543/500) 0) (D : q.Inside 1 (39/100))
    (F : ¬q.Inside 1 (-13/50)) (M : ¬q.Inside (7/20) (7/20)) : q.Inside 1 (2/5) := by
  classical
  obtain ⟨R,rc,rs,rside,rinside,_⟩ := ClosedFrames.canonical_frame q
  have ha : 1<R.side := by rwa [rside]
  have a := (rinside _ _).mpr A
  have s := (rinside _ _).mpr S
  have d := (rinside _ _).mpr D
  have f : ¬R.Inside 1 (-13/50) := fun own => F ((rinside _ _).mp own)
  have m : ¬R.Inside (7/20) (7/20) := fun own => M ((rinside _ _).mp own)
  have result : R.Inside 1 (2/5) := by
    by_cases sign : 0≤R.s
    · have cn : Normal R.c R.s := ⟨sign,by simpa only [abs_of_nonneg sign] using rs,R.unit_normal⟩
      exact False.elim (positive_impossible R cn ha a s f m)
    · have sn : R.s≤0 := by exact (lt_of_not_ge sign).le
      have cn : Normal R.c (-R.s) := ⟨by linarith only [sn],
        by simpa only [abs_of_nonpos sn] using rs,by nlinarith only [R.unit_normal]⟩
      exact negative_point R cn ha a s d f m
  exact (rinside _ _).mp result

#print axioms point
end N12Compact.C1092MMMPRightNearAdvance
