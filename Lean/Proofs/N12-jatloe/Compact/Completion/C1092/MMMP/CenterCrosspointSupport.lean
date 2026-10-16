import S12.SquareSupportBase
import Compact.Completion.C1092.MMMP.CenterCrosspointScalars
import Compact.Completion.C1092.WholeSupports
import Compact.Geometry.ClosedFrames

/-! The complete-square support step of MMMP center-to-crosspoint.
The actual wall square and its center sign are explicit hypotheses. -/
namespace N12Compact.C1092MMMPCenterCrosspointSupport
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports
set_option Elab.async false

theorem negative_axes (C W : OpenSquare) (same : C.side=W.side)
    (cp : 0<C.c) (cs : C.s≤0) (wh : 0≤W.c) (ws : W.s≤0)
    (Q : C.Inside (13/50) 0) (rho : ℝ) (large : 13/50<rho)
    (R : C.Inside 1 rho) (S : W.Inside (543/500) 0)
    (T : W.Inside 1 (13/50))
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) :
    C.loU+C.side≤lower W C.c C.s ∨ upper C W.c W.s≤W.loU := by
  have all := CongruentSAT.faceSeparation_of_disjoint C W same apart
  change pairRadius C W≤|C.c*(centerX W-centerX C)+C.s*(centerY W-centerY C)| ∨
    pairRadius C W≤|-C.s*(centerX W-centerX C)+C.c*(centerY W-centerY C)| ∨
    pairRadius W C≤|W.c*(centerX W-centerX C)+W.s*(centerY W-centerY C)| ∨
    pairRadius W C≤|-W.s*(centerX W-centerX C)+W.c*(centerY W-centerY C)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius C nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX C)+ny*(centerY W-centerY C)|) :=
    separated C W nx ny (by rwa [identity])
  rcases all with cu|cv|wu|wv
  · have sep := split C.c C.s _ (parallel_radius C W) cu
    rw [(ownU C).1,(ownU C).2] at sep
    rcases sep with forward|reverse
    · exact Or.inl forward
    · have bound := (strict_bounds W _ _ C.c C.s C.unit_normal S).2
      exfalso
      linarith only [reverse,bound,Q.1,cp]
  · have sep := split (-C.s) C.c _ (transverse_radius C W) cv
    rw [(ownV C).1,(ownV C).2] at sep
    rcases sep with forward|reverse
    · have bound := (strict_bounds W _ _ (-C.s) C.c
        (by nlinarith only [C.unit_normal]) T).1
      have weight := mul_pos cp (sub_pos.mpr large)
      exfalso
      nlinarith only [forward,bound,R.2.2.2,weight]
    · have bound := (strict_bounds W _ _ (-C.s) C.c
        (by nlinarith only [C.unit_normal]) S).2
      exfalso
      linarith only [reverse,bound,Q.2.2.1,cs]
  · have identity : supportRadius C W.c W.s+supportRadius W W.c W.s=pairRadius W C := by
      rw [add_comm]
      exact parallel_radius W C
    have sep := split W.c W.s _ identity wu
    rw [(ownU W).1,(ownU W).2] at sep
    rcases sep with forward|reverse
    · exact Or.inr forward
    · have bound := (strict_bounds C _ _ W.c W.s W.unit_normal Q).1
      exfalso
      linarith only [reverse,bound,S.2.1,wh]
  · have identity : supportRadius C (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W C := by
      rw [add_comm]
      exact transverse_radius W C
    have sep := split (-W.s) W.c _ identity wv
    rw [(ownV W).1,(ownV W).2] at sep
    rcases sep with forward|reverse
    · have bound := (strict_bounds C _ _ (-W.s) W.c
        (by nlinarith only [W.unit_normal]) R).2
      have weight := mul_nonneg wh (sub_nonneg.mpr large.le)
      exfalso
      nlinarith only [forward,bound,T.2.2.1,weight]
    · have bound := (strict_bounds C _ _ (-W.s) W.c
        (by nlinarith only [W.unit_normal]) Q).1
      exfalso
      linarith only [reverse,bound,S.2.2.2,ws]

private theorem negative_wall (C W : OpenSquare) (c s h b : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (hframe : W.c=h) (bframe : W.s=-b)
    (cn : Normal c s) (sp : 0<s) (small : s≤1/4)
    (hh : 0≤h) (hb : 0≤b) (side : 1<C.side) (same : C.side=W.side)
    (lowerU : -s/2≤C.loU) (lowerV : -(7/20)*(c-s)≤C.loV) (vnegative : C.loV<0)
    (Q : C.Inside (13/50) 0) (rho : ℝ) (large : 13/50<rho)
    (R : C.Inside 1 rho) (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have hn : h^2+b^2=1 := by simpa only [hframe,bframe,neg_sq] using W.unit_normal
  have both := negative_axes C W same (by rwa [cframe]) (by rw [sframe]; linarith only [sp])
    (by rwa [hframe]) (by rw [bframe]; linarith only [hb]) Q rho large R S T apart
  have wallBound := square_support_bound W 1 0 2
    (by intro x y own; simpa only [one_mul,zero_mul,add_zero] using wall x y own)
  have wallCenter : centerX W+W.side*(h+b)/2≤2 := by
    have raw := wallBound
    norm_num [squareRadius,hframe,bframe,abs_of_nonneg hh,abs_of_nonneg hb] at raw
    linarith only [raw]
  have sideW : 1<W.side := by rwa [←same]
  have ownWall : W.loU<2*h-(1+h^2+h*b)/2 := by
    have bound := mul_le_mul_of_nonneg_left wallCenter hh
    have cy := mul_nonneg hb cut
    have penalty : 0<1+h^2+h*b := by nlinarith only [sq_nonneg h,mul_nonneg hh hb]
    have strict := mul_pos (sub_pos.mpr sideW) penalty
    have formula := (ownU W).1
    dsimp [lower,supportRadius] at formula
    rw [show W.c*W.c+W.s*W.s=1 by nlinarith only [W.unit_normal],
      show -W.c*W.s+W.s*W.c=0 by ring] at formula
    norm_num only [abs_one,abs_zero,add_zero,mul_one] at formula
    rw [hframe,bframe] at formula
    nlinarith only [bound,cy,strict,formula]
  let alpha := c*h+s*b
  let delta := s*h-c*b
  have ap : 0<alpha := by
    have sum : 0<h+b := by nlinarith only [hn,hh,hb]
    have first := mul_pos sp sum
    have last := mul_nonneg (sub_nonneg.mpr cn.2.1) hh
    dsimp [alpha]
    nlinarith only [first,last]
  have normalProduct : c*W.c+(-s)*W.s=alpha := by rw [hframe,bframe]; dsimp [alpha]; ring
  have transverseProduct : -c*W.s+(-s)*W.c=-delta := by
    rw [hframe,bframe]; dsimp [delta]; ring
  have wallNormal : lower W c (-s)<1-s/2 := by
    have bound := mul_le_mul_of_nonneg_left wallCenter cp.le
    have cy := mul_nonneg cn.1 cut
    have penalty : 1+c^2+c*s≤c*(h+b)+alpha+|delta| := by
      have raw := C1092ShortWallPenalty.penalty cn hh hb hn
      have absId : |c*b-s*h|=|delta| := by
        dsimp [delta]
        rw [show c*b-s*h=-(s*h-c*b) by ring,abs_neg]
      rw [absId] at raw
      dsimp [alpha]
      nlinarith only [raw]
    have coefficient : 0<c*(h+b)+alpha+|delta| := by
      nlinarith only [penalty,sq_nonneg c,mul_nonneg cp.le cn.1]
    have strict := mul_pos (sub_pos.mpr sideW) coefficient
    have formula : lower W c (-s)=c*centerX W-s*centerY W-
        W.side*(alpha+|delta|)/2 := by
      dsimp [lower,supportRadius]
      rw [normalProduct,transverseProduct,abs_of_pos ap,abs_neg]
      ring
    have margin := mul_nonneg
      (show 0≤1-c by linarith only [cb.2.1])
      (show 0≤3-c-s by linarith only [cb.2.1,small])
    nlinarith only [formula,bound,cy,strict,penalty,margin,cn.2.2]
  rcases both with central|foreign
  · rw [cframe,sframe] at central
    linarith only [central,wallNormal,lowerU,side]
  · have upperU : 1-s/2<C.loU+C.side := by linarith only [lowerU,side]
    rw [hframe,bframe] at foreign
    by_cases order : 0≤delta
    · have upperV : 1-(7/20)*(c-s)<C.loV+C.side := by
        linarith only [lowerV,side]
      have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_le_mul_of_nonneg_left upperV.le order
      have formula : upper C h (-b)=alpha*(C.loU+C.side)+delta*(C.loV+C.side) := by
        rw [(formulas C h (-b)).2]
        rw [show h*C.c+(-b)*C.s=alpha by rw [cframe,sframe]; dsimp [alpha]; ring,
          show -h*C.s+(-b)*C.c=delta by rw [cframe,sframe]; dsimp [delta]; ring,
          max_eq_left ap.le,max_eq_left order]
        ring
      have gap := C1092MMMPCenterCrosspointScalars.first cn small hh hb hn order
      dsimp [alpha,delta] at first last formula
      nlinarith only [foreign,ownWall,first,last,formula,gap]
    · have order : delta≤0 := by exact (lt_of_not_ge order).le
      have first := mul_lt_mul_of_pos_left upperU ap
      have last := mul_nonneg (neg_nonneg.mpr order) (neg_nonneg.mpr vnegative.le)
      have formula : upper C h (-b)=alpha*(C.loU+C.side)+delta*C.loV := by
        rw [(formulas C h (-b)).2]
        rw [show h*C.c+(-b)*C.s=alpha by rw [cframe,sframe]; dsimp [alpha]; ring,
          show -h*C.s+(-b)*C.c=delta by rw [cframe,sframe]; dsimp [delta]; ring,
          max_eq_left ap.le,max_eq_right order]
        ring
      have gap := C1092MMMPCenterCrosspointScalars.second cn small hh hb hn order
      dsimp [alpha,delta] at first last formula
      nlinarith only [foreign,ownWall,first,last,formula,gap]

/-- Reindexing W covers every physical wall orientation, including its axial
limits. C is explicitly the negative canonical representative. -/
theorem impossible (C W : OpenSquare) (c s : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (cn : Normal c s) (sp : 0<s) (small : s≤1/4)
    (side : 1<C.side) (same : C.side=W.side)
    (lowerU : -s/2≤C.loU) (lowerV : -(7/20)*(c-s)≤C.loV) (vnegative : C.loV<0)
    (Q : C.Inside (13/50) 0) (rho : ℝ) (large : 13/50<rho)
    (R : C.Inside 1 rho) (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) : False := by
  obtain ⟨V,vc,vs,vside,_,vcenter,vinside⟩ := exists_positive_frame W
  let B := turnFrame (turnFrame (turnFrame V))
  have bside : B.side=W.side := by simpa [B] using vside
  have binside : ∀ x y, B.Inside x y↔W.Inside x y := by
    intro x y
    simpa [B] using vinside x y
  have bcenter : centerY B=centerY W := by simpa [B] using vcenter
  apply negative_wall C B c s V.s V.c cframe sframe
    (by dsimp [B,turnFrame] <;> ring) (by dsimp [B,turnFrame] <;> ring) cn sp small vs vc
    side (same.trans bside.symm) lowerU lowerV vnegative Q rho large R
    ((binside _ _).mpr S) ((binside _ _).mpr T)
    (fun x y own => wall x y ((binside _ _).mp own))
    (by simpa only [bcenter] using cut)
    (fun x y own => apart x y ⟨own.1,(binside _ _).mp own.2⟩)

#print axioms impossible
end N12Compact.C1092MMMPCenterCrosspointSupport
