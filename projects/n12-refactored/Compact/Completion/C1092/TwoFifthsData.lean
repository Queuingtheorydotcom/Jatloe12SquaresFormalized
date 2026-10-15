import Compact.Completion.C1092.WholeSupports
import Compact.Completion.C1092.WallProfileScalars
import Compact.Geometry.ClosedFrames
import Compact.Geometry.C977CornerCubic
import S12.SquareSupportBase

/-! Literal local input of C1092-TWO-FIFTHS-SLOPE-SQUEEZE. The same
actual right square occurs in both comparisons. The reciprocal-free
angle inequalities are equivalent to the paper's positive ratios.
No G8 choice, side upper cap or E/N disjointness is required. -/
namespace N12Compact.C1092TwoFifths
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false
noncomputable section

structure Southeast (E : OpenSquare) : Prop where
  side : 1<E.side
  cosine : 0<E.c
  sine : 0<E.s
  small : 3*E.s<E.c
  inner : E.Inside 0 (-13/50)
  forward : E.Inside (13/50) 0
  upperV : E.loV+E.side≤0
  floor : E.side*(E.c+E.s)-1<E.s*(E.loU+E.side)+E.c*(E.loV+E.side)

structure Northeast (N : OpenSquare) : Prop where
  side : 1<N.side
  cosine : 0<N.c
  sine : 0<N.s
  canonical : N.s≤N.c
  halfLow : 1+N.c<4*N.s
  halfHigh : 3*N.s≤1+N.c
  lowerU : (2/5)*N.s≤N.loU
  lowerV : (2/5)*N.c-N.s≤N.loV
  upperU : N.loU+N.side≤N.c+N.s
  upperV : N.loV+N.side≤N.c
  marker : N.Inside (7/20) (7/20)
  top : N.Inside (2/5) 1
  sharp : N.Inside (47/100) (3/25)

structure Right (R : OpenSquare) : Prop where
  bar : ∀ y : ℝ,-13/50≤y → y≤2/5 → R.Inside 1 y
  wall : ∀ x y,R.Inside x y → x≤2
  center : 0≤centerY R

structure Input (E N R : OpenSquare) : Prop where
  southeast : Southeast E
  northeast : Northeast N
  right : Right R
  sameER : E.side=R.side
  sameNR : N.side=R.side
  apartER : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)
  apartNR : ∀ x y,¬(N.Inside x y ∧ R.Inside x y)

theorem Right.reframe {R Q : OpenSquare} (h : Right R)
    (same : ∀ x y,Q.Inside x y↔R.Inside x y)
    (center : centerY Q=centerY R) : Right Q where
  bar := fun y low high => (same _ _).mpr (h.bar y low high)
  wall := fun x y own => h.wall x y ((same x y).mp own)
  center := by simpa only [center] using h.center

/-- Canonical face indexing, additionally recording the actual center.
Only whole-square frame turns are used; no physical reflection occurs. -/
theorem canonical_right (R : OpenSquare) :
    ∃ Q : OpenSquare,0<Q.c ∧ |Q.s|≤Q.c ∧ Q.side=R.side ∧
      (∀ x y,Q.Inside x y↔R.Inside x y) ∧ centerY Q=centerY R := by
  obtain ⟨Q,cn,sn,shape,_,cy,same⟩ := exists_positive_frame R
  by_cases order : Q.s≤Q.c
  · have cp : 0<Q.c := by
      apply lt_of_not_ge
      intro bad
      have cz : Q.c=0 := le_antisymm bad cn
      have sz : Q.s=0 := le_antisymm (order.trans bad) sn
      nlinarith only [Q.unit_normal,cz,sz]
    exact ⟨Q,cp,by simpa only [abs_of_nonneg sn] using order,shape,same,cy⟩
  · let T := turnFrame (turnFrame (turnFrame Q))
    have cp : 0<T.c := by
      dsimp [T,turnFrame]
      linarith only [cn,lt_of_not_ge order]
    have canonical : |T.s|≤T.c := by
      dsimp [T,turnFrame]
      rw [abs_of_nonpos (by linarith only [cn])]
      linarith only [lt_of_not_ge order]
    exact ⟨T,cp,canonical,by simpa only [T,turnFrame_side] using shape,
      by intro x y; simpa only [T,turnFrame_inside] using same x y,
      by simpa only [T,turnFrame_centerY] using cy⟩

end
end N12Compact.C1092TwoFifths
