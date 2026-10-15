import Compact.Geometry.FullAuxWallLowerCorner
import Compact.Geometry.C977CornerCubic

/-! Exact narrowing and a strict inward reach for the negative opposite
elbow. Only the actual foreign left auxiliary point is excluded; no saved
angle range or extra wall point is assumed. The input cut is the surviving
full-square separator from C to A. -/
namespace N12Compact.FullAuxWallOppositeEscape
open S12 S12Pilot FourSquareAnchors C977CornerCubic
set_option Elab.async false

private theorem lower_v_margin {c s C S : ℝ}
    (an : Normal c s) (dn : Normal C S) (narrow : 4*s≤c) :
    (13/50)*s≤(c*S+s*C)*(1-S-(13/50)*C) := by
  have db := normal_bounds dn
  have cp : 0≤C := by linarith only [db.1]
  let N := 1-S-(13/50)*C
  have nsmall : (1/10 : ℝ)≤N := by
    dsimp [N]
    linarith only [dn.2.1,db.2.2.2.2.2]
  have coefficient : (13/50 : ℝ)≤(4*S+C)*N := by
    by_cases high : (13/20 : ℝ)≤S
    · have product := mul_nonneg (show 0≤4*S+C by linarith only [dn.1,cp])
        (sub_nonneg.mpr nsmall)
      nlinarith only [product,high,db.1]
    · have upper : S≤13/20 := (lt_of_not_ge high).le
      have first := mul_nonneg (show 0≤4*S+C by linarith only [dn.1,cp])
        (show 0≤N-((37/50)-S) by dsimp [N]; linarith only [db.2.1])
      have second := mul_nonneg
        (show 0≤(37/50 : ℝ)-S by linarith only [upper])
        (sub_nonneg.mpr db.1)
      have square := mul_nonneg dn.1 (sub_nonneg.mpr upper)
      nlinarith only [first,second,square,upper]
  have excess := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr narrow) dn.1)
    ((by norm_num : (0 : ℝ) ≤ 1/10).trans nsmall)
  have weighted := mul_nonneg an.1 (sub_nonneg.mpr coefficient)
  change (13/50)*s≤(c*S+s*C)*N
  apply sub_nonneg.mp
  convert add_nonneg excess weighted using 1 <;> ring

/-- The original lower-U escape is incompatible with every opposite angle
at or above 1/4. One concave quadratic covers that entire arc. -/
private theorem narrow_of_cut {c s C S u v : ℝ}
    (an : Normal c s) (dn : Normal C S) (sp : 0<s)
    (narrow : 4*s≤c) (up : 0<u) (vp : 0<v)
    (lower : 1-C+(13/50)*S<u)
    (cut : (c*C-s*S)*u+(c*S+s*C)*v<(13/50)*s) : 4*S<C := by
  apply lt_of_not_ge
  intro large
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<c := by linarith only [ab.1]
  have dcp : 0<C := by linarith only [db.1]
  have range := mul_nonneg (sub_nonneg.mpr large)
    (show 0≤4*S+C by linarith only [dn.1,dcp])
  have upper : C≤34/35 := by
    apply le_of_not_gt
    intro bad
    have square := mul_pos (sub_pos.mpr bad)
      (show 0<C+(34/35 : ℝ) by linarith only [dcp])
    nlinarith only [square,range,dn.2.2]
  have interval := mul_nonneg (sub_nonneg.mpr db.1) (sub_nonneg.mpr upper)
  have quadratic : (13/150 : ℝ)≤C-(187/200)*C^2 := by
    nlinarith only [interval,upper]
  have alpha1 := mul_nonneg an.1 (sub_nonneg.mpr dn.2.1)
  have alpha2 := mul_nonneg dcp.le (sub_nonneg.mpr narrow)
  have alpha : (3/4)*c*C≤c*C-s*S := by nlinarith only [alpha1,alpha2]
  have coefficientPositive : 0<(3/4 : ℝ)*c*C := by positivity
  have fromLower := mul_lt_mul_of_pos_left lower coefficientPositive
  have fromAlpha := mul_nonneg up.le (sub_nonneg.mpr alpha)
  have fromSlope := mul_nonneg
    (show 0≤(39/200 : ℝ)*c*C by positivity)
    (sub_nonneg.mpr large)
  have fromQuadratic := mul_nonneg
    (show 0≤(3/4 : ℝ)*c by positivity) (sub_nonneg.mpr quadratic)
  have positive := mul_nonneg
    (add_nonneg (mul_nonneg cp.le dn.1) (mul_nonneg an.1 dcp.le)) vp.le
  nlinarith only [fromLower,fromAlpha,fromSlope,fromQuadratic,positive,cut,narrow]

/-- Genuine foreign exclusion narrows the signed opposite square and
forces its strict point (11/10,2). The crosspoint (2,3/2) is retained as
an explicit original-geometry entrance. -/
theorem narrow_and_left (D : OpenSquare) (c s S : ℝ)
    (an : Normal c s) (sp : 0<s) (narrow : 4*s≤c)
    (ds : D.s=-S) (dn : Normal D.c S) (ha : 1<D.side)
    (center : D.Inside 2 2) (bottom : D.Inside 2 (3/2))
    (missing : ¬D.Inside 1 (87/50))
    (cut : (c*D.c-s*S)*(D.loU+D.side-2*(D.c-S))+
      (c*S+s*D.c)*(D.loV+D.side-2*(D.c+S))<(13/50)*s) :
    4*S<D.c ∧ D.Inside (11/10) 2 := by
  have ab := normal_bounds an
  have db := normal_bounds dn
  have cp : 0<c := by linarith only [ab.1]
  have dc : 0<D.c := by linarith only [db.1]
  let u := D.loU+D.side-2*(D.c-S)
  let v := D.loV+D.side-2*(D.c+S)
  let alpha := c*D.c-s*S
  let k := c*S+s*D.c
  change alpha*u+k*v<(13/50)*s at cut
  have up : 0<u := by
    have h := center.2.1
    rw [ds] at h
    dsimp [u]; nlinarith only [h]
  have vp : 0<v := by
    have h := center.2.2.2
    rw [ds,neg_neg] at h
    dsimp [v]; nlinarith only [h]
  have alphaPositive : 0<alpha := by
    have first := mul_nonneg an.1 (sub_nonneg.mpr dn.2.1)
    have second := mul_pos (show 0<c-s by linarith only [narrow,cp]) dc
    dsimp [alpha]; nlinarith only [first,second]
  have kPositive : 0<k := by
    have first := mul_nonneg cp.le dn.1
    have second := mul_pos sp dc
    dsimp [k]; nlinarith only [first,second]
  have upperU : D.c*1+D.s*(87/50)<D.loU+D.side := by
    have h := center.2.1
    rw [ds] at h ⊢
    nlinarith only [h,dc,dn.1,dn.2.1]
  have upperV : -D.s*1+D.c*(87/50)<D.loV+D.side := by
    have h := center.2.2.2
    rw [ds,neg_neg] at h ⊢
    nlinarith only [h,dc,dn.1]
  have lowerU : D.c-(87/50)*S≤D.loU := by
    apply le_of_not_gt
    intro lowerU
    have lowerV : D.loV<S+(87/50)*D.c := by
      apply lt_of_not_ge
      intro escaped
      have below : 1-S-(13/50)*D.c<v := by dsimp [v]; linarith only [escaped,ha]
      have weighted := mul_lt_mul_of_pos_left below kPositive
      have nonnegative := mul_nonneg alphaPositive.le up.le
      have margin := lower_v_margin an dn narrow
      change (13/50)*s≤k*(1-S-(13/50)*D.c) at margin
      have contradiction : (13/50)*s < alpha*u+k*v :=
        (margin.trans_lt weighted).trans_le (le_add_of_nonneg_left nonnegative)
      exact (not_lt_of_ge contradiction.le) cut
    apply missing
    refine ⟨?_,upperU,?_,upperV⟩ <;> rw [ds] <;>
      nlinarith only [lowerU,lowerV]
  have lower : 1-D.c+(13/50)*S<u := by dsimp [u]; linarith only [lowerU,ha]
  have small := narrow_of_cut an dn sp narrow up vp lower cut
  have range := mul_nonneg (sub_nonneg.mpr small.le)
    (show 0≤D.c+4*S by linarith only [dc,dn.1])
  have cosine : (9/10 : ℝ)≤D.c := by
    apply le_of_not_gt
    intro bad
    have square := mul_pos (sub_pos.mpr bad)
      (show 0<(9/10 : ℝ)+D.c by linarith only [dc])
    nlinarith only [square,range,dn.2.2]
  have a1 := mul_nonneg an.1 (sub_nonneg.mpr dn.2.1)
  have a2 := mul_nonneg dc.le (sub_nonneg.mpr narrow)
  have a3 := mul_nonneg cp.le (sub_nonneg.mpr cosine)
  have alphaBound : (27/40)*c≤alpha := by
    dsimp [alpha]; nlinarith only [a1,a2,a3]
  have uSmall : u<(1/10 : ℝ) := by
    apply lt_of_not_ge
    intro big
    have weighted := mul_nonneg alphaPositive.le (sub_nonneg.mpr big)
    have nonnegative := mul_nonneg kPositive.le vp.le
    have scaled : (27/400)*c ≤ alpha/10 := by
      calc
        _ = (1/10)*((27/40)*c) := by ring
        _ ≤ (1/10)*alpha := mul_le_mul_of_nonneg_left alphaBound (by norm_num)
        _ = _ := by ring
    have smaller : (13/50)*s < (27/400)*c := by linarith only [narrow,cp]
    have actualLower : alpha/10 ≤ alpha*u+k*v := by
      calc
        _ = alpha*(1/10) := by ring
        _ ≤ alpha*u := mul_le_mul_of_nonneg_left big alphaPositive.le
        _ ≤ _ := le_add_of_nonneg_right nonnegative
    exact (not_lt_of_ge ((smaller.trans_le scaled).trans_le actualLower).le) cut
  have point : D.Inside (11/10) 2 := by
    have cU := center.2.1
    have cV := center.2.2.2
    have bV := bottom.2.2.1
    rw [ds] at cU cV bV
    refine ⟨?_,?_,?_,?_⟩ <;> rw [ds] <;> dsimp [u] at uSmall <;>
      nlinarith only [uSmall,ha,cU,cV,bV,db.2.1,dc,dn.1,small]
  exact ⟨small,point⟩

#print axioms narrow_and_left
end N12Compact.FullAuxWallOppositeEscape
