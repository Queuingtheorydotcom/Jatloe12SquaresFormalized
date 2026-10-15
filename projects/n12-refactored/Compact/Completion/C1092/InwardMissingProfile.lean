import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! Exact physical faces of a negative inward square missing the center.
The proof stops before label inspection; every exclusion is a point absence
from this square, including tangent points. -/
namespace N12Compact.C1092InwardMissingProfile
open S12 S12Pilot
set_option Elab.async false

structure Profile (q : OpenSquare) : Prop where
  sine : q.s < 0
  lowerV : 0 ≤ q.loV
  lowerU : -(7/20)*(q.c-q.s) ≤ q.loU
  upperU : q.loU+q.side ≤ q.c+(2/5)*q.s
  upperV : q.loV+q.side ≤ q.c-(2/5)*q.s
  outer : q.Inside (13/20) (7/20)
  halfSmall : C1092WallProfileScalars.half q.c (-q.s) < 2/5

theorem profile (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : q.s ≤ 0) (order : -q.s ≤ q.c)
    (M : q.Inside (7/20) (7/20)) (P : q.Inside 0 (13/50))
    (Q : q.Inside (13/50) 0) (O : ¬ q.Inside 0 0)
    (R : ¬ q.Inside 1 (2/5)) (A : ¬ q.Inside (2/5) 1)
    (N : ¬ q.Inside (-7/20) (7/20)) : Profile q := by
  classical
  have cu : q.c ≤ 1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have lowerV : 0 ≤ q.loV := by
    apply le_of_not_gt
    intro h
    apply O
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [P.1,Q.2.1,h,M.2.2.2,cp,sn]
  have sine : q.s < 0 := by nlinarith only [Q.2.2.1,lowerV]
  have chord := short_projections q (7/10) (7/10) (by norm_num)
  have upperU : q.loU+q.side ≤ q.c+(2/5)*q.s := by
    apply le_of_not_gt
    intro h
    apply R
    exact ⟨by linarith only [Q.1,cp,order],by linarith only [h],
      by linarith only [Q.2.2.1,cp,sn],
      by linarith only [lowerV,side,chord.2.2.2,order]⟩
  have aLowerU : q.loU < (2/5)*q.c+q.s := by
    have short := short_projections q (3/5) (-3/5) (by norm_num)
    linarith only [upperU,side,short.2.1]
  have aLowerV : q.loV < -(2/5)*q.s+q.c := by
    linarith only [M.2.2.1,cp,sn]
  have aUpperU : (2/5)*q.c+q.s < q.loU+q.side := by
    apply lt_of_not_ge
    intro high
    have nLower : -(7/20)*q.c+(7/20)*q.s ≤ q.loU ∨
        (7/20)*q.s+(7/20)*q.c ≤ q.loV := by
      by_cases first : -(7/20)*q.c+(7/20)*q.s ≤ q.loU
      · exact Or.inl first
      · apply Or.inr
        apply le_of_not_gt
        intro h
        apply N
        exact ⟨by linarith only [first],by linarith only [M.2.1,cp],
          by linarith only [h],by linarith only [M.2.2.2,sn]⟩
    rcases nLower with first | second
    · linarith only [first,high,side,cu,sn]
    · linarith only [second,Q.2.2.1,M.2.1,high,cp]
  have upperV : q.loV+q.side ≤ q.c-(2/5)*q.s := by
    apply le_of_not_gt
    intro h
    apply A
    exact ⟨by linarith only [aLowerU],by linarith only [aUpperU],
      by linarith only [aLowerV],by linarith only [h]⟩
  have lowerU : -(7/20)*(q.c-q.s) ≤ q.loU := by
    apply le_of_not_gt
    intro h
    have nLower : (7/20)*q.s+(7/20)*q.c ≤ q.loV := by
      apply le_of_not_gt
      intro h'
      apply N
      exact ⟨by linarith only [h],by linarith only [M.2.1,cp],
        by linarith only [h'],by linarith only [M.2.2.2,sn]⟩
    have short := short_projections q (3/4) (13/20) (by norm_num)
    linarith only [nLower,upperV,side,short.2.2.2]
  have outer : q.Inside (13/20) (7/20) := by
    have short := short_projections q (13/20) (7/20) (by norm_num)
    exact ⟨by linarith only [M.1,cp],
      by linarith only [lowerU,cu,side],
      by linarith only [P.2.2.1,cp,sn],
      by linarith only [short.2.2.2,lowerV,side]⟩
  have denominator : 0 < 1+q.c := by linarith only [cp]
  have factor : (1+q.c)*(q.c-(2/5)*q.s-1)=
      (-q.s)*((2/5)*(1+q.c)+q.s) := by nlinarith only [q.unit_normal]
  have positive := mul_pos denominator
    (show 0 < q.c-(2/5)*q.s-1 by linarith only [upperV,side,lowerV])
  have coefficient : 0 < (2/5)*(1+q.c)+q.s := by
    apply (mul_lt_mul_left (by linarith only [sine] : 0 < -q.s)).mp
    nlinarith only [factor,positive]
  have halfSmall : C1092WallProfileScalars.half q.c (-q.s) < 2/5 := by
    dsimp [C1092WallProfileScalars.half]
    apply (div_lt_iff₀ denominator).mpr
    linarith only [coefficient]
  exact ⟨sine,lowerV,lowerU,upperU,upperV,outer,halfSmall⟩

#print axioms profile
end N12Compact.C1092InwardMissingProfile
