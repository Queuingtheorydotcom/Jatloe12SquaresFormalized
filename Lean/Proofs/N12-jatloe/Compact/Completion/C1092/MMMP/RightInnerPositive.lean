import Compact.Completion.C1092.MMMP.RightInwardProfile
import Compact.Completion.C1092.WholeSupports

/-! Once the genuine northeast sign is known, the right inward exclusion
needs only its positive-sign support argument. The right square remains
unrestricted in angle and is reindexed using its actual owned points. -/
namespace N12Compact.C1092MMMPRightInnerPositive
open C977ChainBridge ThreeSquare S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
set_option Elab.async false

private theorem axes (E R : OpenSquare) (same : E.side=R.side)
    (cp : 0<E.c) (sn : 0≤E.s) (bp : 0<R.c) (tn : R.s≤0)
    (M : E.Inside (7/20) (7/20)) (B : E.Inside (13/50) 1)
    (A : R.Inside (13/50) 0) (D : R.Inside 1 (2/5))
    (apart : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y)) :
    upper R (-E.s) E.c≤E.loV ∨ upper E R.c R.s≤R.loU := by
  have all := CongruentSAT.faceSeparation_of_disjoint E R same apart
  change pairRadius E R≤|E.c*(centerX R-centerX E)+E.s*(centerY R-centerY E)| ∨
    pairRadius E R≤|-E.s*(centerX R-centerX E)+E.c*(centerY R-centerY E)| ∨
    pairRadius R E≤|R.c*(centerX R-centerX E)+R.s*(centerY R-centerY E)| ∨
    pairRadius R E≤|-R.s*(centerX R-centerX E)+R.c*(centerY R-centerY E)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius E nx ny+supportRadius R nx ny=radius)
      (sep : radius≤|nx*(centerX R-centerX E)+ny*(centerY R-centerY E)|) :=
    separated E R nx ny (by rwa [identity])
  rcases all with eu|ev|ru|rv
  · have sep := split E.c E.s _ (parallel_radius E R) eu
    have first := strict_bounds E _ _ E.c E.s E.unit_normal B
    have last := strict_bounds R _ _ E.c E.s E.unit_normal A
    have em := strict_bounds E _ _ E.c E.s E.unit_normal M
    have rd := strict_bounds R _ _ E.c E.s E.unit_normal D
    rcases sep with forward|reverse <;> exfalso
    · linarith only [forward,first.2,last.1,sn]
    · linarith only [reverse,em.1,rd.2,cp,sn]
  · have sep := split (-E.s) E.c _ (transverse_radius E R) ev
    rcases sep with forward|reverse
    · have first := (strict_bounds E _ _ (-E.s) E.c
        (by nlinarith only [E.unit_normal]) B).2
      have last := (strict_bounds R _ _ (-E.s) E.c
        (by nlinarith only [E.unit_normal]) A).1
      exfalso
      linarith only [forward,first,last,cp]
    · exact Or.inl (by simpa only [(ownV E).1] using reverse)
  · have identity : supportRadius E R.c R.s+supportRadius R R.c R.s=pairRadius R E := by
      rw [add_comm]; exact parallel_radius R E
    have sep := split R.c R.s _ identity ru
    rcases sep with forward|reverse
    · exact Or.inr (by simpa only [(ownU R).1] using forward)
    · have first := (strict_bounds E _ _ R.c R.s R.unit_normal B).1
      have last := (strict_bounds R _ _ R.c R.s R.unit_normal A).2
      exfalso
      linarith only [reverse,first,last,tn]
  · have identity : supportRadius E (-R.s) R.c+supportRadius R (-R.s) R.c=pairRadius R E := by
      rw [add_comm]; exact transverse_radius R E
    have sep := split (-R.s) R.c _ identity rv
    have first := strict_bounds E _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) B
    have last := strict_bounds R _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) A
    have em := strict_bounds E _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) M
    have rd := strict_bounds R _ _ (-R.s) R.c
      (by nlinarith only [R.unit_normal]) D
    rcases sep with forward|reverse <;> exfalso
    · linarith only [forward,first.2,last.1,bp]
    · linarith only [reverse,em.1,rd.2,bp,tn]

private theorem fixed (E R : OpenSquare) (side : 1<E.side) (same : E.side=R.side)
    (en : Normal E.c E.s) (rn : Normal R.c (-R.s)) (data : C1092MMMPRightInwardProfile.Data R)
    (M : E.Inside (7/20) (7/20)) (B : E.Inside (13/50) 1) (C : E.Inside (2/5) 1)
    (A : R.Inside (13/50) 0) (D : R.Inside 1 (2/5))
    (apart : ∀ x y, ¬(E.Inside x y ∧ R.Inside x y)) : False := by
  have eb := normal_bounds en
  have rb := normal_bounds rn
  have ep : 0<E.c := by linarith only [eb.1]
  have rp : 0<R.c := by linarith only [rb.1]
  have tp : 0< -R.s := by linarith only [data.sineLow]
  let c := E.c
  let s := E.s
  let b := R.c
  let t := -R.s
  let alpha := b*c-t*s
  let k := b*s+t*c
  have ap : 0<alpha := by
    have first := mul_pos (show 0<R.c-(-R.s) by linarith only [data.cosine,data.sineHigh]) ep
    have last := mul_nonneg rn.1 (sub_nonneg.mpr en.2.1)
    dsimp [alpha,b,c,t,s]
    nlinarith only [first,last]
  have kp : 0<k := by
    have first := mul_nonneg rp.le en.1
    have last := mul_pos tp ep
    dsimp [k,b,s,t,c]
    linarith only [first,last]
  have all := axes E R same ep en.1 rp (by linarith only [rn.1]) M B A D apart
  rcases all with centralAxis|wallAxis
  · have support := upper_np R (-s) c (-k) alpha
      (by dsimp [k,b,t,c,s]; ring) (by dsimp [alpha,b,t,c,s]; ring)
      (by linarith only [kp]) ap.le
    have first := mul_lt_mul_of_neg_left A.1 (by linarith only [kp] : -k<0)
    have upperV : 1+t-(13/50)*b<R.loV+R.side := by
      have sideR : 1<R.side := by rwa [←same]
      dsimp [t,b]
      linarith only [data.lowerV,sideR]
    have last := mul_lt_mul_of_pos_left upperV ap
    have bt := mul_nonneg rp.le rn.1
    have tsq := mul_pos (show 0<1/3-(-R.s) by linarith only [data.sineHigh])
      (show 0<1/3+(-R.s) by linarith only [rn.1])
    have a0 : 33/100<b+(37/50)*b*t-(13/50)*b^2-7/20 := by
      dsimp [b,t]
      nlinarith only [data.cosine,bt,rn.2.2,sq_nonneg (-R.s)]
    have b0 : -33/100<9/100-t-(37/50)*t^2+(13/50)*b*t := by
      dsimp [b,t]
      nlinarith only [data.sineHigh,bt,tsq]
    have p1 := mul_pos ep (sub_pos.mpr a0)
    have p2 := mul_nonneg en.1 (sub_nonneg.mpr b0.le)
    have p3 := sub_nonneg.mpr en.2.1
    have identity : -k*((13/50)*b)+alpha*(1+t-(13/50)*b)-(7/20)*(c-s)=
        c*(b+(37/50)*b*t-(13/50)*b^2-7/20)+
          s*(9/100-t-(37/50)*t^2+(13/50)*b*t) := by
      dsimp [k,alpha]
      linear_combination (-(13/50)*s)*rn.2.2
    nlinarith only [centralAxis,support,first,last,p1,p2,p3,identity,M.2.2.1]
  · have support : upper E b (-t)=alpha*(E.loU+E.side)-k*E.loV := by
      rw [(formulas E b (-t)).2,
        show b*E.c+(-t)*E.s=alpha by dsimp [alpha,b,t,c,s]; ring,
        show -b*E.s+(-t)*E.c=-k by dsimp [k,b,t,c,s]; ring,
        max_eq_left ap.le,max_eq_right (by linarith only [kp] : -k≤0)]
      ring
    have first := mul_lt_mul_of_pos_left C.2.1 ap
    have last := mul_lt_mul_of_neg_left M.2.2.1 (by linarith only [kp] : -k<0)
    have cs := mul_nonneg ep.le en.1
    have order := mul_nonneg en.1 (sub_nonneg.mpr en.2.1)
    let coefficient := 7/20+(7/10)*c*s
    have coeffPos : 0<coefficient := by dsimp [coefficient,c,s]; nlinarith only [cs]
    have ratio := mul_pos
      (show 0<(13/37)*b-t by dsimp [b,t]; linarith only [data.upperSlope]) coeffPos
    have correction := mul_nonneg
      (show 0≤b/20+(13/20)*t by dsimp [b,t]; linarith only [rp,rn.1]) order
    have base := mul_pos rp (show 0<63/3700+(131/370)*E.c*E.s by nlinarith only [cs])
    have identity : alpha*((2/5)*c+s)-k*(7/20)*(c-s)-(13/50)*b=
        b*(7/50-s^2/20+(13/20)*c*s)-t*(7/20+(13/20)*s^2+c*s/20) := by
      dsimp [alpha,k]
      linear_combination ((2/5)*b-(7/20)*t)*en.2.2
    dsimp [coefficient,c,s] at ratio
    dsimp [c,s,b,t] at correction base first last wallAxis
    dsimp [c,s,b,t] at support identity ratio
    simp only [neg_neg] at support
    nlinarith only [wallAxis,support,first,last,identity,ratio,correction,base,A.1]

theorem impossible (E W : OpenSquare) (side : 1<E.side) (same : E.side=W.side)
    (en : Normal E.c E.s)
    (M : E.Inside (7/20) (7/20)) (B : E.Inside (13/50) 1) (C : E.Inside (2/5) 1)
    (A : W.Inside (13/50) 0) (S : W.Inside (543/500) 0) (D : W.Inside 1 (2/5))
    (F : ¬W.Inside 1 (-13/50))
    (apart : ∀ x y, ¬(E.Inside x y ∧ W.Inside x y)) : False := by
  obtain ⟨R,rside,rinside,rn,data⟩ := C1092MMMPRightInwardProfile.exists_negative W
    (by rwa [←same]) A S D F (fun own => apart _ _ ⟨M,own⟩)
  exact fixed E R side (same.trans rside.symm) en rn data M B C
    ((rinside _ _).mpr A) ((rinside _ _).mpr D)
    (fun x y own => apart x y ⟨own.1,(rinside x y).mp own.2⟩)

#print axioms impossible
end N12Compact.C1092MMMPRightInnerPositive
