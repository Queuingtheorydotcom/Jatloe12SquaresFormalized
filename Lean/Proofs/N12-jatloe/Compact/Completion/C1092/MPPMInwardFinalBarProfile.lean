import Compact.Completion.C1092.MPPMInwardFinalSuccessor
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! NEGATIVE-SUCCESSOR-BAR-PROFILE, with the actual whole right bar.
Point exclusions are weak and the crossing uses a closed vertex, never
an invented strictly owned vertex. Source only, uncompiled. -/
namespace N12Compact.C1092MPPMInwardFinal
open S12 S12Pilot FourSquareAnchors C977CornerCubic C1092WallProfileScalars
open Completion.OtherCases
set_option Elab.async false

theorem successor_preliminary (E : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s)) (negative : E.s<0)
    (marker : E.Inside (7/20) (-7/20))
    (near : E.Inside (13/50) (-1)) (outer : E.Inside (2/5) (-1))
    (inner : ¬E.Inside 0 (-13/50)) (origin : ¬E.Inside 1 0)
    (corner : ¬E.Inside 1 (-1)) (bottom : ¬E.Inside 0 (-543/500)) :
    -(13/50)*E.s≤E.loU ∧ E.loU+E.side≤E.c-E.s ∧
      -(543/500)*E.c≤E.loV ∧ E.loV+E.side≤-E.s := by
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have first : -(13/50)*E.s≤E.loU := by
    apply le_of_not_gt
    intro lowU
    have cap : E.loV+E.side≤-(13/50)*E.c := by
      apply le_of_not_gt
      intro high
      apply inner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [lowU,marker.2.1,outer.2.2.1,high,ep,en.2.1,negative]
    have topU : E.loU+E.side≤E.c-E.s := by
      apply le_of_not_gt
      intro high
      apply corner
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [outer.1,high,marker.2.2.2,cap,side,eb.2.1,ep,en.2.1,negative]
    have bottomU : -(543/500)*E.s≤E.loU := by
      apply le_of_not_gt
      intro low
      apply bottom
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [low,near.2.1,marker.2.2.2,cap,side,eb.2.1,ep,en.2.1,negative]
    linarith only [bottomU,topU,side,eb.2.1,negative]
  have last : E.loV+E.side≤-E.s := by
    apply le_of_not_gt
    intro high
    apply origin
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [marker.1,outer.2.2.1,first,high,side,eb.2.1,ep,en.2.1,negative]
  have upper : E.loU+E.side≤E.c-E.s := by
    apply le_of_not_gt
    intro high
    apply corner
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [outer.1,high,marker.2.2.2,last,side,eb.2.1,ep,en.2.1,negative]
  have lower : -(543/500)*E.c≤E.loV := by
    apply le_of_not_gt
    intro low
    apply bottom
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [near.2.1,marker.2.2.2,upper,side,low,eb.2.1,ep,en.2.1,negative]
  exact ⟨first,upper,lower,last⟩

private theorem crossing_right (E R : OpenSquare) (X Y : ℝ)
    (closed : ClosedInside E X Y) (marker : E.Inside (7/20) (-7/20))
    (right : 1<X) (low : -2/5<Y) (high : Y<0)
    (bar : ∀ y : ℝ,-2/5≤y → y≤0 → R.Inside 1 y)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) : False := by
  let z := (X-1)/(X-7/20)
  have den : 0<X-7/20 := by linarith only [right]
  have zp : 0<z := div_pos (by linarith only [right]) den
  have zu : z<1 := (div_lt_one den).mpr (by linarith)
  have identity : z*(X-7/20)=X-1 := div_mul_cancel₀ _ den.ne'
  have coordinate : (1-z)*X+z*(7/20)=1 := by nlinarith only [identity]
  have lower := mul_nonneg (show 0≤1-z by linarith only [zu])
    (show 0≤Y+2/5 by linarith only [low])
  have upper := mul_nonpos_of_nonneg_of_nonpos
    (show 0≤1-z by linarith only [zu]) high.le
  have own := WallProfile.strict_closed_segment E X Y (7/20) (-7/20) z
    closed marker zp zu
  rw [coordinate] at own
  exact apart _ _ ⟨own,bar _ (by nlinarith only [lower,zp]) (by nlinarith only [upper,zp])⟩

theorem successor_bar_cap (E R : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s)) (negative : E.s<0)
    (marker : E.Inside (7/20) (-7/20))
    (near : E.Inside (13/50) (-1)) (outer : E.Inside (2/5) (-1))
    (inner : ¬E.Inside 0 (-13/50)) (origin : ¬E.Inside 1 0)
    (corner : ¬E.Inside 1 (-1)) (bottom : ¬E.Inside 0 (-543/500))
    (bar : ∀ y : ℝ,-2/5≤y → y≤0 → R.Inside 1 y)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) :
    E.loV+E.side≤-E.s-(2/5)*E.c := by
  have faces := successor_preliminary E side en negative marker near outer inner origin corner bottom
  have eb := normal_bounds en
  have ep : 0<E.c := by linarith only [eb.1]
  have tp : 0< -E.s := by linarith only [negative]
  have missing : ¬E.Inside 1 (-2/5) := fun own => apart _ _ ⟨own,bar _ le_rfl (by norm_num)⟩
  have modes : E.loU+E.side≤E.c-(2/5)*E.s ∨
      E.loV+E.side≤-E.s-(2/5)*E.c := by
    by_cases cap : E.loU+E.side≤E.c-(2/5)*E.s
    · exact Or.inl cap
    · right
      apply le_of_not_gt
      intro high
      apply missing
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [marker.1,outer.2.2.1,cap,high,ep,en.2.1,negative]
  rcases modes with upperU|done
  · exfalso
    have width : 1<E.c-(7/50)*E.s := by linarith only [faces.1,upperU,side]
    have data := quarter_data E.c (-E.s) ep.le en.1 en.2.2
    let z := half E.c (-E.s)
    have den : 0<1+z^2 := by nlinarith only [sq_nonneg z]
    have identity : (1+z^2)*(E.c-(7/50)*E.s-1)=2*z*(7/50-z) := by
      nlinarith only [data.2.2.2.1,data.2.2.2.2]
    have positive := mul_pos den (sub_pos.mpr width)
    have smallHalf : z<7/50 := by
      apply lt_of_not_ge
      intro large
      have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤2*z by linarith only [data.1])
        (show 7/50-z≤0 by linarith only [large])
      nlinarith only [bad,identity,positive]
    have extra := mul_nonneg en.1 (sq_nonneg z)
    have small : -E.s<7/25 := by nlinarith only [data.2.2.2.2,smallHalf,extra]
    let J := E.loU+E.side
    let D := E.loV+E.side
    let X := E.c*J-E.s*D
    let Y := E.s*J+E.c*D
    have closed : ClosedInside E X Y := WallProfile.vertex E J D
      ⟨by dsimp [J]; linarith only [E.side_pos],le_rfl⟩
      ⟨by dsimp [D]; linarith only [E.side_pos],le_rfl⟩
    have upperY : Y<0 := by
      have first := mul_nonneg tp.le (sub_nonneg.mpr faces.1)
      have last := mul_nonneg ep.le (sub_nonneg.mpr faces.2.2.2)
      have strict := mul_pos tp (show 0<E.side-E.c by linarith only [side,eb.2.1])
      dsimp [Y,J,D]
      nlinarith only [first,last,strict,sq_nonneg E.s]
    have lowerY : -2/5<Y := by
      have first := mul_nonneg tp.le (sub_nonneg.mpr upperU)
      have last := mul_nonneg ep.le (sub_nonneg.mpr faces.2.2.1)
      have strict := mul_pos ep (sub_pos.mpr side)
      have cosine := mul_nonneg ep.le (show 0≤1-E.c by linarith only [eb.2.1])
      have cross := mul_nonneg tp.le (show 0≤1-E.c by linarith only [eb.2.1])
      have square := mul_nonneg (show 0≤7/25+E.s by linarith only [small])
        (show 0≤7/25-E.s by linarith only [negative])
      dsimp [Y,J,D]
      nlinarith only [first,last,strict,cosine,cross,square,small,E.unit_normal]
    have right : 1<X := by
      have first := mul_nonneg ep.le (sub_nonneg.mpr faces.1)
      have last := mul_nonneg tp.le (sub_nonneg.mpr faces.2.2.1)
      have strict := mul_pos (sub_pos.mpr side)
        (show 0<E.c-E.s by linarith only [ep,tp])
      have chord := mul_nonneg
        (show 0≤32/25-(E.c-E.s) by linarith only [eb.2.1,small])
        (show 0≤E.c-E.s-1 by linarith only [eb.2.2.2.2.1])
      have arc : 1-(50/57)*E.c*E.s≤E.c-E.s := by nlinarith only [chord,E.unit_normal]
      have cross := mul_pos ep tp
      dsimp [X,J,D]
      nlinarith only [first,last,strict,arc,cross]
    exact crossing_right E R X Y closed marker right lowerY upperY bar apart
  · exact done

theorem negative_successor (E R : OpenSquare) (side : 1<E.side)
    (en : Normal E.c (-E.s)) (negative : E.s<0)
    (marker : E.Inside (7/20) (-7/20))
    (near : E.Inside (13/50) (-1)) (outer : E.Inside (2/5) (-1))
    (halfpoint : E.Inside (1/2) (-1))
    (inner : ¬E.Inside 0 (-13/50)) (origin : ¬E.Inside 1 0)
    (corner : ¬E.Inside 1 (-1)) (bottom : ¬E.Inside 0 (-543/500))
    (bar : ∀ y : ℝ,-2/5≤y → y≤0 → R.Inside 1 y)
    (apart : ∀ x y,¬(E.Inside x y ∧ R.Inside x y)) : NegativeSuccessor E := by
  have faces := successor_preliminary E side en negative marker near outer inner origin corner bottom
  exact ⟨en,marker,near,halfpoint,faces.1,faces.2.1,faces.2.2.1,
    successor_bar_cap E R side en negative marker near outer inner origin corner bottom bar apart⟩

#print axioms successor_preliminary
#print axioms successor_bar_cap
#print axioms negative_successor
end N12Compact.C1092MPPMInwardFinal
