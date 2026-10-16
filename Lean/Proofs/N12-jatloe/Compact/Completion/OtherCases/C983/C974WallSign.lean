import Compact.Completion.OtherCases.C983.C974WallNegativeCaps
import Compact.Completion.OtherCases.C983.C974WallSignScalars

/-! The two remaining actual-axis comparisons of
MISSING-CORNER-WALL-SIGN §§1.3--1.6, then its Theorem 1.
No canonical orientation of K is assumed in the negative-W comparison.
Source translation only; this has not been replayed in Lean. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false
noncomputable section

theorem negative_wall_impossible (K W : OpenSquare) (e : Input K W)
    (lp : 0<K.c) (hp : 0<K.s) (cap : K.loV+K.side≤0)
    (t : ℝ) (frame : W.s= -t) (dp : 0<W.c) (tn : 0≤t) (order : t≤W.c) : False := by
  let l := K.c
  let h := K.s
  let d := W.c
  let a := K.side
  let U := K.loU
  let B := K.loV+K.side
  let L := W.loU-W.c
  let H := W.loV-t
  let x := h/(1+l)
  let y := t/(1+d)
  let k := l*d-h*t
  let s := l*t+h*d
  have ku : l^2+h^2=1 := K.unit_normal
  have wu : d^2+t^2=1 := by simpa only [frame,neg_sq] using W.unit_normal
  have side : 1<a := e.sideLarge
  have Bcap : B≤0 := cap
  have wall : a*l-1≤h*U+l*B := singleton_wall K W e
  have caps := wall_negative_caps K W e t frame dp tn order
  have slope : 77*t<20*d := caps.2.1
  have vCap : H+a≤t+d/2 := by
    dsimp only [H,a]
    rw [e.sameSide]
    linarith only [caps.2.2.1]
  have eitherCap : L+a≤d ∨ H+a≤t := by
    rcases caps.2.2.2 with first | last
    · left
      dsimp only [L,a]
      rw [e.sameSide]
      linarith only [first]
    · right
      dsimp only [H,a]
      rw [e.sameSide]
      linarith only [last]
  obtain ⟨xp,half,lc,hs⟩ := quadrant_half l h lp hp ku
  have relation : x*(1+l)=h := div_mul_cancel₀ _ (by positivity : (1+l:ℝ)≠0)
  have hu : h<1 := by nlinarith only [ku,sq_pos_of_pos lp,hp]
  have du : d≤1 := by nlinarith only [wu,sq_nonneg t,dp]
  have tu : t<1/3 := by linarith only [slope,du]
  have dl : 9/10<d := by
    have t2 := mul_nonneg (show 0≤1/3-t by linarith only [tu])
      (show 0≤1/3+t by positivity)
    nlinarith only [t2,wu,dp]
  have sp : 0<s := add_pos_of_nonneg_of_pos (mul_nonneg lp.le tn) (mul_pos hp dp)
  have origin := e.o
  simp only [OpenSquare.Inside,InBands,frame,mul_one,mul_zero,add_zero,neg_neg] at origin
  have Ln : L<0 := by
    change W.loU-W.c<0
    linarith only [origin.1]
  have p := e.p
  dsimp [OpenSquare.Inside,InBands] at p
  have Un : U<0 := by
    change K.loU<0
    linarith only [p.1,hp]
  have width : 1-x<U+a := by
    have wallB := mul_nonneg lp.le (neg_nonneg.mpr Bcap)
    have strict := mul_pos (sub_pos.mpr side) (add_pos lp hp)
    have scaled : 0<h*(U+a-(1-x)) := by nlinarith only [wall,wallB,strict,half]
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hp).mp scaled)
  have axes := separating_u K W e lp hp dp cap
    (fun sep => by
      have cone := separator_cone K W e (-W.s) W.c (by nlinarith only [W.unit_normal]) sep
      rw [frame] at cone
      linarith only [cone.2.2,slope,dp])
    (fun sep => by
      have cone := separator_cone K W e W.s (-W.c) (by nlinarith only [W.unit_normal]) sep
      rw [frame] at cone
      linarith only [cone.1,tn])
  rcases axes with alongK | alongW
  · have cone := separator_cone K W e K.c K.s K.unit_normal alongK
    have angle : 43*h<90*l := by linarith only [cone.2.2]
    have kp : 0<k := by
      have first := mul_nonneg tn (show 0≤90*l-43*h by linarith only [angle])
      have last := mul_pos lp (show 0<20*d-77*t by linarith only [slope])
      have positive := mul_pos lp dp
      dsimp only [k]
      nlinarith only [first,last,positive]
    have xu : x<2/3 := by
      by_contra no
      have bad : 2/3≤x := le_of_not_gt no
      have scaled := mul_nonneg (show 0≤1+l by positivity) (sub_nonneg.mpr bad)
      have lower : 2*(1+l)≤3*h := by nlinarith only [scaled,relation]
      have lLower : 43/92<l := by linarith only [lower,angle]
      have square := mul_nonneg (show 0≤3*h-2*(1+l) by linarith only [lower])
        (show 0≤3*h+2*(1+l) by positivity)
      nlinarith only [square,ku,lLower]
    have lowerForm : lower W K.c K.s=l+k*L+s*H := by
      rw [C981CompletionSupportForms.lower_in_bands,frame]
      change (l*d+h*(-t))*(W.loU+W.side/2)+(-l*(-t)+h*d)*(W.loV+W.side/2)-
        W.side/2*(|l*d+h*(-t)|+|-l*(-t)+h*d|)=l+k*L+s*H
      rw [show l*d+h*(-t)=k by dsimp only [k]; ring,
        show -l*(-t)+h*d=s by dsimp only [s]; ring,abs_of_pos kp,abs_of_pos sp]
      dsimp only [k,s,L,H,l,h,d]
      linear_combination K.c*wu
    rw [upper_self,lowerForm] at alongK
    change U+a≤l+k*L+s*H at alongK
    rcases eitherCap with uCap | cHigh
    · have first := mul_nonneg kp.le (sub_nonneg.mpr uCap)
      have last := mul_nonneg sp.le (sub_nonneg.mpr vCap)
      have excess := mul_pos (sub_pos.mpr side) (add_pos kp sp)
      have necessary : 1-l-x+k*(1-d)+s*(1-t-d/2)<0 := by
        nlinarith only [alongK,width,first,last,excess]
      have yd : 0<1+d := by positivity
      have yn : 0≤y := div_nonneg tn yd.le
      have yr : y*(1+d)=t := div_mul_cancel₀ _ yd.ne'
      have yu : y<1/7 := by
        apply (div_lt_iff₀ yd).mpr
        linarith only [slope,du]
      have yh : t*y=1-d := by
        apply (mul_right_cancel₀ yd.ne')
        linear_combination t*yr+wu
      have dc : d=(1-y^2)/(1+y^2) := by
        apply (eq_div_iff (by positivity : (1+y^2:ℝ)≠0)).mpr
        linear_combination y*yr+yh
      have ts : t=2*y/(1+y^2) := by
        apply (eq_div_iff (by positivity : (1+y^2:ℝ)≠0)).mpr
        linear_combination y*yh-yr
      have positive := negative_wall_scalar l h d t x y xp xu.le yn yu.le lc hs dc ts
      exact (not_lt_of_ge positive.le) necessary
    · have first := mul_neg_of_pos_of_neg kp Ln
      have last := mul_nonneg sp.le (sub_nonneg.mpr cHigh)
      have excess := mul_pos sp (sub_pos.mpr side)
      have necessary : 1-x<l-s*(1-t) := by
        nlinarith only [alongK,width,first,last,excess]
      have sum : 1≤l+h := by nlinarith only [ku,mul_pos lp hp,lp,hp]
      have defect : x*(1-h)≤h/2 := by
        have weight := mul_nonneg xp.le (show 0≤l+2*h-1 by linarith only [sum,hp])
        nlinarith only [weight,relation]
      have dWidth : 3/5<d*(1-t) := by
        have weight := mul_pos dp (show 0<1/3-t by linarith only [tu])
        nlinarith only [weight,dl]
      have scalar : 3*h/5<s*(1-t) := by
        have first := mul_pos hp (show 0<d*(1-t)-3/5 by linarith only [dWidth])
        have last := mul_nonneg (mul_nonneg lp.le tn) (show 0≤1-t by linarith only [tu])
        dsimp only [s]
        nlinarith only [first,last]
      nlinarith only [necessary,defect,scalar,half,hp]
  · have point := (strict_bounds W _ _ W.c W.s W.unit_normal e.o).1
    have strict : upper K W.c W.s<d := lt_of_le_of_lt alongW (by simpa only [mul_one,mul_zero,add_zero] using point)
    by_cases sign : 0≤k
    · have upperForm : upper K W.c W.s=k*U+a*(k+s)-s*B := by
        rw [C981CompletionSupportForms.upper_in_bands,frame]
        change (d*l+(-t)*h)*(U+a/2)+(-d*h+(-t)*l)*(K.loV+a/2)+
          a/2*(|d*l+(-t)*h|+|-d*h+(-t)*l|)=k*U+a*(k+s)-s*B
        rw [show d*l+(-t)*h=k by dsimp only [k]; ring,
          show -d*h+(-t)*l= -s by dsimp only [s]; ring,
          abs_of_nonneg sign,abs_of_nonpos (neg_nonpos.mpr sp.le)]
        dsimp only [B,a]
        ring
      rw [upperForm] at strict
      have wallWeight := mul_nonneg sign (sub_nonneg.mpr wall)
      have capWeight := mul_nonneg (add_nonneg (mul_nonneg hp.le sp.le) (mul_nonneg sign lp.le))
        (neg_nonneg.mpr Bcap)
      have sepWeight := mul_pos hp (sub_pos.mpr strict)
      have coefficient : 0<h*(k+s)+k*l := by positivity
      have excess := mul_pos (sub_pos.mpr side) coefficient
      have necessary : h*(k*(1-x)+s-d)<0 := by
        nlinarith only [wallWeight,capWeight,sepWeight,excess,
          show k*(h*x-(1-l))=0 by rw [half]; ring]
      have identity : k*(1-x)+s-d=(1-h)*(d*x+t) := by
        dsimp only [k,s]
        linear_combination (d+t)*half-d*relation
      have positive := mul_pos (show 0<1-h by linarith only [hu])
        (add_pos_of_pos_of_nonneg (mul_pos dp xp) tn)
      rw [identity] at necessary
      exact (not_lt_of_ge (mul_nonneg hp.le positive.le)) necessary
    · have kn : k<0 := lt_of_not_ge sign
      have upperForm : upper K W.c W.s=k*U+s*(a-B) := by
        rw [C981CompletionSupportForms.upper_in_bands,frame]
        change (d*l+(-t)*h)*(U+a/2)+(-d*h+(-t)*l)*(K.loV+a/2)+
          a/2*(|d*l+(-t)*h|+|-d*h+(-t)*l|)=k*U+s*(a-B)
        rw [show d*l+(-t)*h=k by dsimp only [k]; ring,
          show -d*h+(-t)*l= -s by dsimp only [s]; ring,
          abs_of_neg kn,abs_of_nonpos (neg_nonpos.mpr sp.le)]
        dsimp only [B,a]
        ring
      rw [upperForm] at strict
      have first := mul_pos_of_neg_of_neg kn Un
      have last := mul_pos sp (show 0<a-B-1 by linarith only [side,Bcap])
      have lower : s<d := by nlinarith only [strict,first,last]
      have relative := mul_neg_of_pos_of_neg lp kn
      have height := mul_pos dp (show 0<1-h by linarith only [hu])
      have sphere : d*(l^2+h^2)=d := by rw [ku]; ring
      have scaled := mul_pos hp (sub_pos.mpr lower)
      dsimp only [k,s] at relative scaled
      nlinarith only [relative,height,sphere,scaled]

/-- WALL-SIGN Theorem 1 in the original physical coordinates. -/
theorem wall_canonical_positive (K W : OpenSquare) (e : Input K W)
    (cp : 0<W.c) (canonical : |W.s|≤W.c) : 0<W.s := by
  by_contra no
  have sn : W.s≤0 := le_of_not_gt no
  obtain ⟨R,shape,same,lp,hp,cap⟩ := singleton_quadrant K W e
  have raw := e.reframeK shape same
  exact negative_wall_impossible R W raw lp hp cap (-W.s) (by ring) cp
    (neg_nonneg.mpr sn) (by linarith only [(abs_le.mp canonical).1])

/-- Both canonical signs are derived from raw ownership and the actual
wall. The strict angle bound for K is a separate MIDPOINT prerequisite. -/
theorem positive_frames (K W : OpenSquare) (e : Input K W) :
    ∃ A B : OpenSquare, A.side=K.side ∧ B.side=W.side ∧
      (∀ x y,A.Inside x y↔K.Inside x y) ∧ (∀ x y,B.Inside x y↔W.Inside x y) ∧
      0<A.s ∧ A.s≤A.c ∧ 0<B.s ∧ B.s≤B.c := by
  obtain ⟨A,ap,arange,ashape,asame,_⟩ := ClosedFrames.canonical_frame K
  obtain ⟨B,bp,brange,bshape,bsame,_⟩ := ClosedFrames.canonical_frame W
  have raw := (e.reframeK ashape asame).reframeW bshape bsame
  have bs := wall_canonical_positive A B raw bp brange
  have as := singleton_canonical_positive A B raw ap arange bp bs.le ((abs_le.mp brange).2)
  exact ⟨A,B,ashape,bshape,asame,bsame,as,(abs_le.mp arange).2,bs,(abs_le.mp brange).2⟩

end
#print axioms wall_canonical_positive
#print axioms positive_frames
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
