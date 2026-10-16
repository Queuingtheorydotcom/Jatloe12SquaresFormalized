import Compact.Completion.C1092.MixedCornerAxes
import Compact.Geometry.ClosedFrames

/-! The actual mixed wall cannot be disjoint from a corner owning both
vertical anchors while that corner omits the indicated upper point.
No wall or center cut is assumed in this local two-square theorem. -/
namespace N12Compact.C1092MixedCornerObstruction
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
open C1092MixedCornerSupports
set_option Elab.async false

private theorem nonnegative (L K : OpenSquare) (side : 1<L.side)
    (same : L.side=K.side) (dn : Normal L.c L.s) (rp : 0<L.s)
    (cn : Normal K.c K.s) (G : L.Inside 0 (2/5))
    (face : -(2/5)*L.c≤L.loV) (H : K.Inside 0 (1/2))
    (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have dp : 0<L.c := by linarith only [db.1]
  have cp : 0<K.c := by linarith only [cb.1]
  have sideK : 1<K.side := by rwa [←same]
  have capU : K.loU+K.side≤(1/5)*K.c+K.s := by
    apply le_of_not_gt
    intro failure
    apply missing
    dsimp [OpenSquare.Inside,InBands] at H P ⊢
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [P.1,P.2.2.2,H.2.2.1,failure,cp,cn.1,cn.2.1]
  have sBound : K.s≤3/4 := by
    nlinarith only [(C1092MixedCornerScalars.elementary cn).2.1,cn.1]
  have negativeU : K.loU<0 := by linarith only [capU,sideK,cb.2.1,sBound]
  have upperU : K.loU<(1/5)*K.c+K.s-1 := by linarith only [capU,sideK]
  have lowerV : K.loV<K.c/2 := by linarith only [H.2.2.1]
  have upperV : K.c<K.loV+K.side := by linarith only [P.2.2.2]
  have J : (2/5)*L.s<L.loU+L.side := by linarith only [G.2.1]
  have capL := upper_cap L side dn rp G face (fun h => apart _ _ ⟨h,H⟩)
  have axes := C1092MixedCornerAxes.alternatives L K side same dn rp cp G face H apart
  rcases axes with axis | axis | axis
  · let alpha := L.c*K.c+L.s*K.s
    let delta := L.s*K.c-L.c*K.s
    have ap : 0<alpha := add_pos_of_pos_of_nonneg (mul_pos dp cp) (mul_nonneg rp.le cn.1)
    have du : L.c*K.c+L.s*K.s=alpha := rfl
    have dv : -L.c*K.s+L.s*K.c=delta := by dsimp [delta]; ring
    by_cases sign : 0≤delta
    · have support := lower_nn K L.c L.s alpha delta du dv ap.le sign
      have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_le_mul_of_nonneg_left lowerV.le sign
      have bound : lower K L.c L.s<alpha*((1/5)*K.c+K.s-1)+delta*(K.c/2) := by
        rw [support]
        exact add_lt_add_of_lt_of_le first last
      have positive := sub_pos.mpr ((J.trans_le axis).trans bound)
      have identity : alpha*((1/5)*K.c+K.s-1)+delta*(K.c/2)-(2/5)*L.s=
          L.c*((1/5)*K.c^2+(1/2)*K.c*K.s-K.c)+
            L.s*(1/10+(1/2)*K.s^2-K.s+(1/5)*K.c*K.s) := by
        dsimp [alpha,delta]
        linear_combination (1/2)*L.s*cn.2.2
      rw [identity] at positive
      exact (not_lt_of_ge (C1092MixedCornerScalars.nonnegative_pair dn cn rp).le) positive
    · have sign' : delta≤0 := (lt_of_not_ge sign).le
      have support := lower_pn K L.c L.s alpha delta du dv ap.le sign'
      have first := mul_neg_of_pos_of_neg ap negativeU
      have last := mul_nonpos_of_nonpos_of_nonneg sign' (cp.le.trans upperV.le)
      have negative : lower K L.c L.s<0 := by rw [support]; exact add_neg_of_neg_of_nonpos first last
      have positive : 0<lower K L.c L.s :=
        (mul_pos (by norm_num : (0:ℝ)<2/5) rp).trans (J.trans_le axis)
      exact (not_lt_of_ge negative.le) positive
  · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
    linarith only [bound,axis,upperU,cb.2.1,cb.2.2.2.1]
  · have bound := up_left L side dn rp G face capL K.c K.s cp cn.1
    linarith only [axis,bound,lowerV]

private theorem nonpositive (L K : OpenSquare) (side : 1<L.side)
    (same : L.side=K.side) (dn : Normal L.c L.s) (rp : 0<L.s)
    (cn : Normal K.c (-K.s)) (G : L.Inside 0 (2/5))
    (face : -(2/5)*L.c≤L.loV) (H : K.Inside 0 (1/2))
    (P : K.Inside 0 1) (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  let d := L.c
  let r := L.s
  let c := K.c
  let s := -K.s
  let alpha := d*c-r*s
  let beta := d*s+r*c
  have db := normal_bounds dn
  have cb := normal_bounds cn
  have dp : 0<d := by dsimp [d]; linarith only [db.1]
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have an : 0≤alpha := by
    calc
      alpha = d*(c-s)+s*(d-r) := by dsimp [alpha]; ring
      _ ≥ 0 := add_nonneg (mul_nonneg dp.le (sub_nonneg.mpr cn.2.1))
        (mul_nonneg cn.1 (sub_nonneg.mpr dn.2.1))
  have bp : 0<beta := add_pos_of_nonneg_of_pos (mul_nonneg dp.le cn.1) (mul_pos rp cp)
  have sideK : 1<K.side := by rwa [←same]
  have du : L.c*K.c+L.s*K.s=alpha := by dsimp [alpha,d,r,c,s]; ring
  have dv : -L.c*K.s+L.s*K.c=beta := by dsimp [beta,d,r,c,s]; ring
  have support := lower_nn K L.c L.s alpha beta du dv an bp.le
  have J : (2/5)*r<L.loU+L.side := by dsimp [r]; linarith only [G.2.1]
  have lowV : K.loV<c/2 := by dsimp [c]; linarith only [H.2.2.1]
  have lowU : K.loU< -s := by dsimp [s]; linarith only [P.1]
  have exits : K.loU+K.side≤(1/5)*c-s ∨ K.loV+K.side≤c+(1/5)*s := by
    by_cases first : K.loU+K.side≤(1/5)*c-s
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro second
      apply missing
      dsimp [OpenSquare.Inside,InBands]
      dsimp [c,s] at first second lowU lowV
      refine ⟨?_,?_,?_,?_⟩ <;>
        linarith only [first,second,lowU,lowV,cp,cn.1]
  have axes := C1092MixedCornerAxes.alternatives L K side same dn rp cp G face H apart
  rcases exits with upperU | upperV
  · have ratio : s<(2/5)*c := by
      have owned := H.2.1
      change K.c*0+K.s*(1/2)<K.loU+K.side at owned
      dsimp [s,c] at upperU ⊢
      linarith only [upperU,owned]
    have margin := C1092MixedCornerScalars.upper_u_pair dn cn rp ratio
    have U : K.loU<(1/5)*c-s-1 := by linarith only [upperU,sideK]
    rcases axes with axis | axis | axis
    · have first := mul_le_mul_of_nonneg_left U.le an
      have last := mul_lt_mul_of_pos_left lowV bp
      have bound : lower K L.c L.s<alpha*((1/5)*c-s-1)+beta*(c/2) := by
        rw [support]
        exact add_lt_add_of_le_of_lt first last
      have positive := sub_pos.mpr ((J.trans_le axis).trans bound)
      have identity : alpha*((1/5)*c-s-1)+beta*(c/2)-(2/5)*r=
          d*((1/5)*c^2-(1/2)*c*s-c)+r*(1/10+(1/2)*s^2+s-(1/5)*c*s) := by
        dsimp [alpha,beta]
        linear_combination (1/2)*r*cn.2.2
      rw [identity] at positive
      exact (not_lt_of_ge margin.2.2.le) positive
    · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
      linarith only [axis,bound,H.1,cn.1]
    · have forward := upper_nn L s c beta alpha
        (by dsimp [beta,d,r,c,s]; ring) (by dsimp [alpha,d,r,c,s]; ring) bp.le an
      have first := mul_lt_mul_of_pos_left J bp
      have last := mul_le_mul_of_nonneg_left
        (show 1-(2/5)*d≤L.loV+L.side by dsimp [d]; linarith only [face,side]) an
      have bound : beta*((2/5)*r)+alpha*(1-(2/5)*d)<upper L s c := by
        rw [forward]
        exact add_lt_add_of_lt_of_le first last
      have common := C1092MixedCornerScalars.common dn rp
      have positive : 0<c*(d-9/10+(4/5)*r^2)-s*(r*(1-(4/5)*d)) := by
        calc
          _ = c*(d-9/10+(4/5)*r^2-(2/5)*(r*(1-(4/5)*d)))+
              ((2/5)*c-s)*(r*(1-(4/5)*d)) := by ring
          _ > 0 := add_pos
            (mul_pos cp ((show (0:ℝ)<1/50 by norm_num).trans_le common.2.2.2))
            (mul_pos (sub_pos.mpr ratio) common.2.1)
      have identity : beta*((2/5)*r)+alpha*(1-(2/5)*d)-c/2=
          c*(d-9/10+(4/5)*r^2)-s*(r*(1-(4/5)*d)) := by
        dsimp [alpha,beta,d,r]
        linear_combination -(2/5)*c*dn.2.2
      have half : c/2<upper L s c := (sub_pos.mp (by rw [identity]; exact positive)).trans bound
      change upper L s c≤K.loV at axis
      exact (not_lt_of_ge (axis.trans lowV.le)) half
  · have V : K.loV<c+(1/5)*s-1 := by linarith only [upperV,sideK]
    rcases axes with axis | axis | axis
    · have first := mul_le_mul_of_nonneg_left lowU.le an
      have last := mul_lt_mul_of_pos_left V bp
      have bound : lower K L.c L.s<alpha*(-s)+beta*(c+(1/5)*s-1) := by
        rw [support]
        exact add_lt_add_of_le_of_lt first last
      have positive := sub_pos.mpr ((J.trans_le axis).trans bound)
      have identity : alpha*(-s)+beta*(c+(1/5)*s-1)-(2/5)*r=
          d*((1/5)*s^2-s)+r*(3/5-c+(1/5)*c*s) := by
        dsimp [alpha,beta]
        linear_combination r*cn.2.2
      rw [identity] at positive
      exact (not_lt_of_ge (C1092MixedCornerScalars.upper_v_pair dn cn rp).le) positive
    · have bound := (strict_bounds L _ _ K.c K.s K.unit_normal G).2
      linarith only [axis,bound,H.1,cn.1]
    · have bound := (strict_bounds L _ _ (-K.s) K.c
        (by nlinarith only [K.unit_normal]) G).2
      dsimp [s,c] at V
      linarith only [axis,bound,V,cb.2.1,cb.2.2.2.1]

theorem impossible (L K : OpenSquare) (side : 1<L.side) (same : L.side=K.side)
    (dn : Normal L.c L.s) (rp : 0<L.s)
    (G : L.Inside 0 (2/5)) (face : -(2/5)*L.c≤L.loV)
    (H : K.Inside 0 (1/2)) (P : K.Inside 0 1)
    (missing : ¬K.Inside (1/5) 1)
    (apart : ∀ x y, ¬(L.Inside x y ∧ K.Inside x y)) : False := by
  obtain ⟨R,rc,range,rside,rinside,_⟩ := ClosedFrames.canonical_frame K
  have sameR : L.side=R.side := same.trans rside.symm
  have h := (rinside _ _).mpr H
  have p := (rinside _ _).mpr P
  have missingR : ¬R.Inside (1/5) 1 := fun owned => missing ((rinside _ _).mp owned)
  have apartR : ∀ x y, ¬(L.Inside x y ∧ R.Inside x y) :=
    fun x y owned => apart x y ⟨owned.1,(rinside x y).mp owned.2⟩
  by_cases sign : 0≤R.s
  · exact nonnegative L R side sameR dn rp
      ⟨sign,(abs_le.mp range).2,R.unit_normal⟩ G face h p missingR apartR
  · exact nonpositive L R side sameR dn rp
      ⟨by linarith only [sign],by linarith only [(abs_le.mp range).1],
        by nlinarith only [R.unit_normal]⟩ G face h p missingR apartR

#print axioms impossible
end N12Compact.C1092MixedCornerObstruction
