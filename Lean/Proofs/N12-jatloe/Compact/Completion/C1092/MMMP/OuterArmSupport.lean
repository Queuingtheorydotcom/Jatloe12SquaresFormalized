import Compact.Completion.C1092.MMMP.OuterArmScalars
import Compact.Completion.C1092.MMMP.PhysicalWallSupport
import Compact.Completion.C1092.MMMP.CenterCrosspointSupport

/-! Complete physical support comparison for a centered negative outer
arm and its actual wall neighbor. Both relative-angle orders and every
wall orientation are covered, with true wall and center hypotheses. -/
namespace N12Compact.C1092MMMPOuterArmSupport
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
set_option Elab.async false

private theorem fixed (C W : OpenSquare) (c s h b : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (hframe : W.c=h) (bframe : W.s=-b)
    (cn : Normal c s) (sp : 0<s) (hh : 0≤h) (hb : 0≤b)
    (side : 1<C.side) (same : C.side=W.side)
    (lowerV : -(7/20)*(c-s)≤C.loV) (negativeV : C.loV<0)
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have hn : h^2+b^2=1 := by simpa only [hframe,bframe,neg_sq] using W.unit_normal
  have sideW : 1<W.side := by rwa [←same]
  have wh : 0≤W.c := by rwa [hframe]
  have ws : W.s≤0 := by rw [bframe]; linarith only [hb]
  let alpha := c*h+s*b
  let delta := s*h-c*b
  have ap : 0<alpha := by
    have sum : 0<h+b := by nlinarith only [hn,hh,hb]
    have first := mul_pos sp sum
    have last := mul_nonneg (sub_nonneg.mpr cn.2.1) hh
    dsimp [alpha]
    nlinarith only [first,last]
  have ownWall := C1092MMMPPhysicalWallSupport.own_lt W sideW wh ws wall cut
  rw [hframe,bframe] at ownWall
  have ownNormal : lower W c (-s)<c-(2/5)*s := by
    have bound := C1092MMMPPhysicalWallSupport.lower_le W wh ws wall cut c (-s) cp.le
      (by linarith only [cn.1])
    rw [hframe,bframe] at bound
    have penalty := C1092ShortWallPenalty.penalty cn hh hb hn
    have absId : |c*b-s*h|=|delta| := by
      dsimp [delta]
      rw [show c*b-s*h=-(s*h-c*b) by ring,abs_neg]
    rw [absId] at penalty
    have norm : 1+c^2+c*s≤c*(h+b)+alpha+|delta| := by
      dsimp [alpha]
      nlinarith only [penalty]
    have strict := mul_pos (sub_pos.mpr sideW)
      (show 0<c*(h+b)+alpha+|delta| by
        nlinarith only [norm,sq_nonneg c,mul_nonneg cp.le cn.1])
    have absU : |c*h+(-s)*(-b)|=alpha := by
      rw [abs_of_pos (by dsimp [alpha] at ap; nlinarith only [ap])]
      dsimp [alpha]
      ring
    have absV : |-c*(-b)+(-s)*h|=|delta| := by
      rw [show -c*(-b)+(-s)*h=-delta by dsimp [delta]; ring,abs_neg]
    rw [absU,absV] at bound
    have endpoint := C1092MMMPOuterArmScalars.endpoint cn
    nlinarith only [bound,strict,norm,endpoint]
  have all := C1092MMMPCenterCrosspointSupport.negative_axes C W same
    (by rwa [cframe]) (by rw [sframe]; linarith only [sp]) wh ws Q (2/5) (by norm_num) R S T apart
  have upperU : c-(2/5)*s<C.loU+C.side := by
    have h := R.2.1
    rw [cframe,sframe] at h
    nlinarith only [h]
  rcases all with central|foreign
  · rw [cframe,sframe] at central
    linarith only [central,ownNormal,upperU]
  · rw [hframe,bframe] at foreign
    by_cases order : 0≤delta
    · have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_le_mul_of_nonneg_left
        (show 1-(7/20)*(c-s)≤C.loV+C.side by linarith only [lowerV,side]) order
      have formula : upper C h (-b)=alpha*(C.loU+C.side)+delta*(C.loV+C.side) := by
        rw [(formulas C h (-b)).2,
          show h*C.c+(-b)*C.s=alpha by rw [cframe,sframe]; dsimp [alpha]; ring,
          show -h*C.s+(-b)*C.c=delta by rw [cframe,sframe]; dsimp [delta]; ring,
          max_eq_left ap.le,max_eq_left order]
        ring
      have identity : alpha*(c-(2/5)*s)+delta*(1-(7/20)*(c-s))=
          h*(c^2-(3/4)*c*s+s+(7/20)*s^2)+
            b*((13/20)*c*s-(2/5)*s^2-c+(7/20)*c^2) := by
        dsimp [alpha,delta]
        ring
      have gap := C1092MMMPOuterArmScalars.first cn sp hh hb hn order
      nlinarith only [foreign,ownWall,first,last,formula,gap,identity]
    · have order : delta≤0 := by exact (lt_of_not_ge order).le
      have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_nonneg_of_nonpos_of_nonpos order negativeV.le
      have formula : upper C h (-b)=alpha*(C.loU+C.side)+delta*C.loV := by
        rw [(formulas C h (-b)).2,
          show h*C.c+(-b)*C.s=alpha by rw [cframe,sframe]; dsimp [alpha]; ring,
          show -h*C.s+(-b)*C.c=delta by rw [cframe,sframe]; dsimp [delta]; ring,
          max_eq_left ap.le,max_eq_right order]
        ring
      have identity : alpha*(c-(2/5)*s)=
          h*(c^2-(2/5)*c*s)+b*(c*s-(2/5)*s^2) := by
        dsimp [alpha]
        ring
      have gap := C1092MMMPOuterArmScalars.second cn hh hb hn order
      nlinarith only [foreign,ownWall,first,last,formula,gap,identity]

theorem impossible (C W : OpenSquare) (c s : ℝ) (cframe : C.c=c) (sframe : C.s=-s)
    (cn : Normal c s) (sp : 0<s) (side : 1<C.side) (same : C.side=W.side)
    (lowerV : -(7/20)*(c-s)≤C.loV) (negativeV : C.loV<0)
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  obtain ⟨V,vc,vs,vside,_,vcenter,vinside⟩ := exists_positive_frame W
  let B := turnFrame (turnFrame (turnFrame V))
  have bside : B.side=W.side := by simpa [B] using vside
  have binside : ∀ x y, B.Inside x y↔W.Inside x y := by
    intro x y
    simpa [B] using vinside x y
  have bcenter : centerY B=centerY W := by simpa [B] using vcenter
  exact fixed C B c s V.s V.c cframe sframe
    (by dsimp [B,turnFrame]; ring) (by dsimp [B,turnFrame])
    cn sp vs vc side (same.trans bside.symm) lowerV negativeV Q R
    ((binside _ _).mpr S) ((binside _ _).mpr T)
    (fun x y own => wall x y ((binside _ _).mp own))
    (by simpa only [bcenter] using cut)
    (fun x y own => apart x y ⟨own.1,(binside _ _).mp own.2⟩)

#print axioms impossible
end N12Compact.C1092MMMPOuterArmSupport
