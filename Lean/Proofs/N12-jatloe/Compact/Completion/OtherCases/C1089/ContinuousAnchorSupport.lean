import Compact.Completion.OtherCases.C1089.ContinuousAnchorScalars
import Compact.Completion.C1092.MMMP.PhysicalWallSupport
import Compact.Completion.C1092.MMMP.CenterCrosspointSupport

/-! The complete physical support step of INWARD-EXTENDED-ANCHOR-CENTER.
Both separating sources and both relative-angle orders use the same
actual W, its one real wall x≤2, and its center sign. The central lower
face is nonnegative only because the center was assumed missing.
Source translation only, not a compilation receipt. -/
namespace N12Compact.Completion.OtherCases.C1089.ContinuousAnchorSupport
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
set_option Elab.async false

private theorem fixed (C W : OpenSquare) (c s h b : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (hframe : W.c=h) (bframe : W.s=-b)
    (cn : Normal c s) (sp : 0<s) (hh : 0≤h) (hb : 0≤b)
    (side : 1<C.side) (same : C.side=W.side)
    (lowerV : 0≤C.loV) (upperV : C.loV<(13/50)*s)
    (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y,W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) : False := by
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
    dsimp only [alpha]
    nlinarith only [first,last]
  have ownWall := C1092MMMPPhysicalWallSupport.own_lt W sideW wh ws wall cut
  rw [hframe,bframe] at ownWall
  have ownNormal : lower W c (-s)<c-(2/5)*s := by
    have bound := C1092MMMPPhysicalWallSupport.lower_le W wh ws wall cut c (-s) cp.le
      (by linarith only [cn.1])
    rw [hframe,bframe] at bound
    have penalty := C1092ShortWallPenalty.penalty cn hh hb hn
    have absId : |c*b-s*h|=|delta| := by
      dsimp only [delta]
      rw [show c*b-s*h=-(s*h-c*b) by ring,abs_neg]
    rw [absId] at penalty
    have norm : 1+c^2+c*s≤c*(h+b)+alpha+|delta| := by
      dsimp only [alpha]
      nlinarith only [penalty]
    have strict := mul_pos (sub_pos.mpr sideW)
      (show 0<c*(h+b)+alpha+|delta| by
        nlinarith only [norm,sq_nonneg c,mul_nonneg cp.le cn.1])
    have absU : |c*h+(-s)*(-b)|=alpha := by
      rw [abs_of_pos (by dsimp only [alpha] at ap; nlinarith only [ap])]
      dsimp only [alpha]
      ring
    have absV : |-c*(-b)+(-s)*h|=|delta| := by
      rw [show -c*(-b)+(-s)*h=-delta by dsimp only [delta]; ring,abs_neg]
    rw [absU,absV] at bound
    have endpoint := C1092MMMPOuterArmScalars.endpoint cn
    nlinarith only [bound,strict,norm,endpoint]
  have all := C1092MMMPCenterCrosspointSupport.negative_axes C W same
    (by rwa [cframe]) (by rw [sframe]; linarith only [sp]) wh ws Q
    (2/5) (by norm_num) R S T apart
  have upperU : c-(2/5)*s<C.loU+C.side := by
    have own := R.2.1
    rw [cframe,sframe] at own
    nlinarith only [own]
  rcases all with central | foreign
  · rw [cframe,sframe] at central
    linarith only [central,ownNormal,upperU]
  · rw [hframe,bframe] at foreign
    by_cases order : 0≤delta
    · have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_le_mul_of_nonneg_left
        (show 1≤C.loV+C.side by linarith only [lowerV,side]) order
      have formula : upper C h (-b)=alpha*(C.loU+C.side)+delta*(C.loV+C.side) := by
        rw [(formulas C h (-b)).2,
          show h*C.c+(-b)*C.s=alpha by rw [cframe,sframe]; dsimp only [alpha]; ring,
          show -h*C.s+(-b)*C.c=delta by rw [cframe,sframe]; dsimp only [delta]; ring,
          max_eq_left ap.le,max_eq_left order]
        ring
      have identity : alpha*(c-(2/5)*s)+delta =
          h*(c^2-(2/5)*c*s+s)+b*(c*s-(2/5)*s^2-c) := by
        dsimp only [alpha,delta]
        ring
      have gap := ContinuousAnchorScalars.first cn sp hh hb hn order
      nlinarith only [foreign,ownWall,first,last,formula,gap,identity]
    · have order : delta≤0 := (lt_of_not_ge order).le
      have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_le_mul_of_nonpos_left upperV.le order
      have formula : upper C h (-b)=alpha*(C.loU+C.side)+delta*C.loV := by
        rw [(formulas C h (-b)).2,
          show h*C.c+(-b)*C.s=alpha by rw [cframe,sframe]; dsimp only [alpha]; ring,
          show -h*C.s+(-b)*C.c=delta by rw [cframe,sframe]; dsimp only [delta]; ring,
          max_eq_left ap.le,max_eq_right order]
        ring
      have identity : alpha*(c-(2/5)*s)+(13/50)*s*delta =
          h*(1-(37/50)*s^2-(2/5)*c*s)+b*((37/50)*c*s-(2/5)*s^2) := by
        dsimp only [alpha,delta]
        linear_combination h*cn.2.2
      have gap := ContinuousAnchorScalars.second cn hh hb hn order
      nlinarith only [foreign,ownWall,first,last,formula,gap,identity]

/-- The full physical wall-orientation cover, including axial endpoints. -/
theorem impossible (C W : OpenSquare) (cn : Normal C.c (-C.s))
    (sign : C.s<0) (side : 1<C.side) (same : C.side=W.side)
    (lowerV : 0≤C.loV) (Q : C.Inside (13/50) 0) (R : C.Inside 1 (2/5))
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y,W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) : False := by
  obtain ⟨V,vc,vs,vside,_,vcenter,vinside⟩ := exists_positive_frame W
  let B := turnFrame (turnFrame (turnFrame V))
  have bside : B.side=W.side := by simpa [B] using vside
  have binside : ∀ x y,B.Inside x y↔W.Inside x y := by
    intro x y
    simpa [B] using vinside x y
  have bcenter : centerY B=centerY W := by simpa [B] using vcenter
  exact fixed C B C.c (-C.s) V.s V.c rfl (by ring)
    (by dsimp only [B,turnFrame]; ring) (by dsimp only [B,turnFrame])
    cn (by linarith only [sign]) vs vc side (same.trans bside.symm) lowerV
    (by have own := Q.2.2.1; nlinarith only [own]) Q R
    ((binside _ _).mpr S) ((binside _ _).mpr T)
    (fun x y own => wall x y ((binside _ _).mp own))
    (by simpa only [bcenter] using cut)
    (fun x y own => apart x y ⟨own.1,(binside _ _).mp own.2⟩)

#print axioms impossible
end N12Compact.Completion.OtherCases.C1089.ContinuousAnchorSupport
