import Compact.Completion.C1092.MPPMActualPositiveOrder
import Compact.Completion.C1092.WholeSupports
import S12.SquareSupportBase

/-! POSITIVE-ORIGIN-OWNED-WALL-ANGLE Theorem 1 and its literal Q4/Q8
application. The real wall is applied to the same entire negative wall
square whose two faces occur in the support comparison. A finite algebraic
difference replaces the half-angle division in the first normal. All closed
canonical endpoints and weak point/face contacts are retained.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMPositiveOriginWallAngle
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MPPMEntrance C1092WallCycle C1092WallSymmetry
open C1092TwoFifths.Support
set_option Elab.async false
noncomputable section

private theorem axes (C L : OpenSquare) (same : C.side=L.side)
    (cn : Normal C.c C.s) (sp : 0<C.s) (ln : Normal L.c (-L.s))
    (P : C.Inside (-1) (-13/50)) (D : C.Inside (-1) 0)
    (W : L.Inside (-543/500) 0) (Q : L.Inside (-1) (13/50))
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) :
    upper C (-C.s) C.c≤lower L (-C.s) C.c ∨
      upper C (-L.c) (-L.s)≤lower L (-L.c) (-L.s) := by
  have cp : 0<C.c := by linarith only [(normal_bounds cn).1]
  have dp : 0<L.c := by linarith only [(normal_bounds ln).1]
  have cone (nx ny : ℝ) (unit : nx^2+ny^2=1)
      (sep : upper C nx ny≤lower L nx ny) : nx<0 ∧ 0<ny := by
    have first := (strict_bounds C _ _ nx ny unit D).2
    have last := (strict_bounds L _ _ nx ny unit W).1
    have lower := (strict_bounds C _ _ nx ny unit P).2
    have higher := (strict_bounds L _ _ nx ny unit Q).1
    constructor <;> linarith only [first,last,lower,higher,sep]
  have all := CongruentSAT.faceSeparation_of_disjoint C L same apart
  change pairRadius C L≤|C.c*(centerX L-centerX C)+C.s*(centerY L-centerY C)| ∨
    pairRadius C L≤|-C.s*(centerX L-centerX C)+C.c*(centerY L-centerY C)| ∨
    pairRadius L C≤|L.c*(centerX L-centerX C)+L.s*(centerY L-centerY C)| ∨
    pairRadius L C≤|-L.s*(centerX L-centerX C)+L.c*(centerY L-centerY C)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius C nx ny+supportRadius L nx ny=radius)
      (sep : radius≤|nx*(centerX L-centerX C)+ny*(centerY L-centerY C)|) :=
    separated C L nx ny (by rwa [identity])
  rcases all with cu|cv|lu|lv
  · rcases split _ _ _ (parallel_radius C L) cu with first|last
    · have no := cone C.c C.s C.unit_normal first
      exact False.elim (by linarith only [no.1,cp])
    · have no := cone (-C.c) (-C.s) (by nlinarith only [C.unit_normal])
        (reverse C L _ _ last)
      exact False.elim (by linarith only [no.2,sp])
  · rcases split _ _ _ (transverse_radius C L) cv with first|last
    · exact Or.inl first
    · have no := cone C.s (-C.c) (by nlinarith only [C.unit_normal])
        (by simpa only [neg_neg] using reverse C L _ _ last)
      exact False.elim (by linarith only [no.2,cp])
  · have radius : supportRadius C L.c L.s+supportRadius L L.c L.s=pairRadius L C := by
      rw [add_comm]
      exact parallel_radius L C
    rcases split _ _ _ radius lu with first|last
    · have no := cone L.c L.s L.unit_normal first
      exact False.elim (by linarith only [no.1,dp])
    · exact Or.inr (reverse C L _ _ last)
  · have radius : supportRadius C (-L.s) L.c+supportRadius L (-L.s) L.c=pairRadius L C := by
      rw [add_comm]
      exact transverse_radius L C
    rcases split _ _ _ radius lv with first|last
    · have no := cone (-L.s) L.c (by nlinarith only [L.unit_normal]) first
      exact False.elim (by linarith only [no.1,ln.1])
    · have no := cone L.s (-L.c) (by nlinarith only [L.unit_normal])
        (by simpa only [neg_neg] using reverse C L _ _ last)
      exact False.elim (by linarith only [no.2,dp])

theorem steep (C L : OpenSquare) (side : 1<C.side) (same : C.side=L.side)
    (cn : Normal C.c C.s) (sp : 0<C.s) (ln : Normal L.c (-L.s))
    (P : C.Inside (-1) (-13/50)) (D : C.Inside (-1) 0)
    (cap : C.loU+C.side≤-(13/50)*C.c)
    (W : L.Inside (-543/500) 0) (Q : L.Inside (-1) (13/50))
    (Z : ¬L.Inside (-543/500) 1)
    (wall : ∀ x y,L.Inside x y→-2≤x)
    (apart : ∀ x y,¬(C.Inside x y ∧ L.Inside x y)) :
    5*L.c<12*(-L.s) := by
  let c := C.c
  let s := C.s
  let d := L.c
  let t := -L.s
  have cb := normal_bounds cn
  have lb := normal_bounds ln
  have cp : 0<c := by dsimp [c]; linarith only [cb.1]
  have dp : 0<d := by dsimp [d]; linarith only [lb.1]
  have tn : 0≤t := ln.1
  have du : d^2+t^2=1 := ln.2.2
  have length : 1<L.side := by rwa [←same]
  apply lt_of_not_ge
  intro bad
  change 12*t≤5*d at bad
  have near : 12/13≤d := by
    apply le_of_not_gt
    intro low
    have first := mul_nonneg (show 0≤5*d-12*t by linarith only [bad])
      (show 0≤5*d+12*t by positivity)
    have last := mul_pos (show 0<12/13-d by linarith only [low])
      (show 0<12/13+d by positivity)
    nlinarith only [du,first,last]
  have slopeSquare := mul_nonneg (show 0≤5*d-12*t by linarith only [bad])
    (show 0≤5*d+12*t by positivity)
  have tSmall : t≤5/13 := by
    apply le_of_not_gt
    intro high
    have gap := mul_pos (show 0<t-5/13 by linarith only [high])
      (show 0<t+5/13 by positivity)
    nlinarith only [du,slopeSquare,gap]
  have noD : ¬L.Inside (-1) 0 := fun own => apart _ _ ⟨D,own⟩
  have capU : L.loU+L.side≤-d := by
    apply le_of_not_gt
    intro high
    apply noD
    refine ⟨?_,?_,?_,?_⟩ <;>
      dsimp [d,t] at * <;> linarith only [W.1,W.2.2.1,Q.2.2.2,high,dp,tn]
  have wallSupport := square_support_bound L (-1) 0 2
    (by intro x y own; have point := wall x y own; linarith only [point])
  have wallLower : -2≤lower L 1 0 := by
    dsimp [lower,supportRadius,squareRadius] at wallSupport ⊢
    simp only [zero_mul,add_zero,neg_mul,neg_neg,one_mul,abs_neg] at wallSupport ⊢
    linarith only [wallSupport]
  have wallFormula := lower_nn L 1 0 d t (by dsimp [d]; ring)
    (by dsimp [t]; ring) dp.le tn
  have floor : -2≤d*L.loU+t*L.loV := by rwa [wallFormula] at wallLower
  have tp : 0<t := by
    apply lt_of_not_ge
    intro no
    have zero : t=0 := le_antisymm no tn
    have one : d=1 := by nlinarith only [du,zero,dp]
    rw [zero,one] at floor
    rw [one] at capU
    linarith only [floor,capU,length]
  have capV : L.loV+L.side≤d-(543/500)*t := by
    apply le_of_not_gt
    intro high
    apply Z
    refine ⟨?_,?_,?_,?_⟩ <;>
      dsimp [d,t] at * <;>
      linarith only [capU,length,high,W.2.1,W.2.2.1,dp,tn,tSmall,lb.2.1]
  let k := c*d-s*t
  let ell := s*d+c*t
  have kLow : (49/120)*d≤k := by
    have first := mul_nonneg (show 0≤c-s by exact sub_nonneg.mpr cn.2.1) tn
    have last := mul_nonneg cp.le (show 0≤5*d-12*t by linarith only [bad])
    have scale := mul_nonneg dp.le (show 0≤c-7/10 by exact sub_nonneg.mpr cb.1)
    dsimp [k]
    nlinarith only [first,last,scale]
  have kp : 0<k := lt_of_lt_of_le (by positivity) kLow
  have ep : 0<ell := by
    have first := mul_pos sp dp
    have last := mul_pos cp tp
    dsimp [ell,c,s,d,t] at *
    linarith only [first,last]
  rcases axes C L same cn sp ln P D W Q apart with transverse|longitudinal
  · have formula := lower_np L (-C.s) C.c (-ell) k
      (by dsimp [ell,c,s,d,t]; ring) (by dsimp [k,c,s,d,t]; ring)
      (by linarith only [ep]) kp.le
    have floorWeight := mul_le_mul_of_nonpos_left floor (show -ell≤0 by linarith only [ep])
    have capWeight := mul_le_mul_of_nonneg_left capV cp.le
    have coefficient : ell*t+k*d=c := by
      dsimp [ell,k,c,s,d,t]
      linear_combination C.c*ln.2.2
    have formulaWeight := congrArg (fun z : ℝ => d*z) formula
    have coefficientWeight := congrArg (fun z : ℝ => z*L.loV) coefficient
    have strict := mul_pos (sub_pos.mpr length)
      (show 0<ell*d+c by positivity)
    have negative := mul_pos (mul_pos cp tp)
      (show 0<d-457/500 by linarith only [near])
    have remainder := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤1-d by exact sub_nonneg.mpr lb.2.1)
      (show s*d-c≤0 by
        have first := mul_nonneg cn.1 (sub_nonneg.mpr lb.2.1)
        dsimp [c,s,d] at *
        nlinarith only [first,cn.2.1])
    have identity : 2*ell+c*(d-(543/500)*t)-ell*d-c-d*s=
        c*t*(457/500-d)+(1-d)*(s*d-c) := by dsimp [ell]; ring
    rw [(ownV C).2] at transverse
    have Dheight : s<C.loV+C.side := by dsimp [s]; linarith only [D.2.2.2]
    have sepWeight := mul_le_mul_of_nonneg_left transverse dp.le
    have pointWeight := mul_lt_mul_of_pos_left Dheight dp
    nlinarith only [formulaWeight,floorWeight,capWeight,coefficientWeight,strict,negative,
      remainder,identity,sepWeight,pointWeight]
  · have formula := upper_np C (-L.c) (-L.s) (-k) ell
      (by dsimp [k,c,s,d,t]; ring) (by dsimp [ell,c,s,d,t]; ring)
      (by linarith only [kp]) ep.le
    have ownLower : lower L (-L.c) (-L.s)=-(L.loU+L.side) := by
      rw [lower_neg,(ownU L).2]
    have low := (strict_bounds L _ _ (-L.c) (-L.s)
      (by nlinarith only [L.unit_normal]) W).1
    have capWeight := mul_le_mul_of_nonpos_left cap (show -k≤0 by linarith only [kp])
    have Dheight : s<C.loV+C.side := by dsimp [s]; linarith only [D.2.2.2]
    have heightWeight := mul_lt_mul_of_pos_left Dheight ep
    have strict := mul_pos (sub_pos.mpr side) kp
    have factor : 13/50≤1-(37/50)*c := by dsimp [c]; linarith only [cb.2.1]
    have product := mul_le_mul_of_nonneg_right factor kp.le
    have lower := mul_le_mul_of_nonneg_left kLow (by norm_num : (0:ℝ)≤13/50)
    have identity : k*(1+(13/50)*c)+ell*s-(543/500)*d=
        (1-(37/50)*c)*k-(43/500)*d := by
      dsimp [k,ell,c,s,d,t]
      linear_combination L.c*cn.2.2
    nlinarith only [longitudinal,formula,low,capWeight,heightWeight,strict,
      product,lower,identity,dp]

structure ActualLeftFrame (p : NormalizedPacking) (L : OpenSquare) : Prop where
  side : L.side=(owners p 8).side
  actual : ∀ x y,L.Inside x y↔(owners p 8).Inside (2+x) (2+y)

/-- No cap is assumed in the original application: the ordinary actual
points and omitted forward point produce it in the same Q4 frame. The
excluded upper point is original marker 7 in the genuine paired Q3. -/
theorem actual_steep (p : NormalizedPacking) (hf : codedMarkerFamily p=family)
    (hb : WallContext p mppm) (h : C1092MPPMActualPositiveOrder.Ordinary p)
    (missing : ¬(owners p 4).Inside (87/50) 2)
    (origin : (owners p 4).Inside 1 2)
    (C : OpenSquare) (frame : C1092MPPMPositiveSeedsActual.ActualFrame p C)
    (cn : Normal C.c C.s) (sp : 0<C.s)
    (L : OpenSquare) (left : ActualLeftFrame p L) (ln : Normal L.c (-L.s)) :
    5*L.c<12*(-L.s) := by
  have side : 1<C.side := by
    rw [frame.side]
    change 1<(p.square _).side
    rw [p.congruent]
    exact p.side_gt_one
  have same : C.side=L.side := frame.side.trans
    (((p.congruent _).trans (p.congruent _).symm).trans left.side.symm)
  have far := (C1092MPPMActualPositiveOrder.far_points p hf hb h).2.1
  have profile := C1092MPPMPositiveSeedsActual.missing_profile p hf hb
    h.southwest.1 h.southwest.2 missing far C frame cn
  have W : (owners p 8).Inside (457/500) 2 := by
    have own := (owners_markers p hf 8 12).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  have K : (owners p 3).Inside (457/500) 3 := by
    have own := (owners_markers p hf 3 7).mpr (by decide +kernel)
    simpa [Owns,marker] using own
  apply steep C L side same cn sp ln
  · apply (frame.actual _ _).mpr; norm_num; exact h.southwest.1
  · apply (frame.actual _ _).mpr; norm_num; exact origin
  · exact profile.upperU
  · apply (left.actual _ _).mpr; norm_num; exact W
  · apply (left.actual _ _).mpr; norm_num; exact (wall_auxiliaries p hb).1
  · intro own
    have original := (left.actual _ _).mp own
    norm_num at original
    exact owners_disjoint p hf 8 3 (by decide) _ _ ⟨original,K⟩
  · intro x y own
    have wall := (p.contained _ _ _ ((left.actual _ _).mp own)).1
    linarith only [wall]
  · exact fun x y both => owners_disjoint p hf 4 8 (by decide) _ _
      ⟨(frame.actual _ _).mp both.1,(left.actual _ _).mp both.2⟩

end
#print axioms steep
#print axioms actual_steep
end N12Compact.C1092MPPMPositiveOriginWallAngle
