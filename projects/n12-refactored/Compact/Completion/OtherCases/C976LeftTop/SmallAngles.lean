import Compact.Completion.OtherCases.C976LeftTop.TopFaces

/-! Section 3: the complete small left-angle interval uses only the
actual marker, high point and real top wall. -/
namespace N12Compact.Completion.OtherCases.C976LeftTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open OrdinaryLeftTop
set_option Elab.async false

private theorem small_residual (l h C S : ℝ) (lp : 0<l) (hp : 0<h)
    (unit : l^2+h^2=1) (low : (21/65)*l<h) (high : h≤l/3)
    (cn : 0≤C) (sp : 0<S) (unitW : C^2+S^2=1) (slope : C≤(2/3)*S) :
    0<C+S-1+S^2*((2/5)*l*h-(13/20)*h^2)-
      C*S*(61/100+(2/5)*h^2+(13/20)*l*h) := by
  have squares := mul_nonneg (show 0≤l-3*h by linarith only [high])
    (show 0≤l+3*h by linarith only [lp,hp])
  have hSmall : h^2≤1/10 := by nlinarith only [squares,unit]
  have lLarge : 9/10≤l^2 := by linarith only [hSmall,unit]
  have crossSquare := mul_nonneg (show 0≤l-3*h by linarith only [high])
    (show 0≤3*l-h by linarith only [high,lp])
  have crossSmall : l*h≤3/10 := by nlinarith only [crossSquare,unit]
  have crossLarge := mul_pos lp (show 0<h-(8/25)*l by linarith only [low,lp])
  have hComparison := mul_nonneg hp.le (show 0≤l-3*h by linarith only [high])
  have first : 1/20<(2/5)*l*h-(13/20)*h^2 := by
    nlinarith only [crossLarge,lLarge,hComparison]
  have last : 61/100+(2/5)*h^2+(13/20)*l*h≤169/200 := by
    linarith only [hSmall,crossSmall]
  have bounds := ShallowTopExitScalars.wall_bounds C S cn sp unitW slope
  have sumUpper := CommonCases.CanonicalProjection.before S C (4/5) (3/5) 1 1
    (by nlinarith only [unitW]) (by norm_num) (by linarith only [slope,sp])
    (by norm_num) (by norm_num)
  have product := mul_nonneg cn sp.le
  have sumLower : 1≤C+S := by nlinarith only [unitW,product,cn,sp]
  have gap := mul_nonneg (show 0≤7/5-(C+S) by linarith only [sumUpper])
    (sub_nonneg.mpr sumLower)
  have arc : (5/6)*C*S≤C+S-1 := by nlinarith only [gap,unitW]
  have cross : C*S≤1/2 := by nlinarith only [unitW,sq_nonneg (C-S)]
  have sineSquare : 16/25≤S^2 := by nlinarith only [bounds.2.1,sp]
  have aWeight := mul_nonneg (sq_nonneg S) (sub_nonneg.mpr first.le)
  have bWeight := mul_nonneg product (sub_nonneg.mpr last)
  nlinarith only [arc,cross,sineSquare,aWeight,bWeight]

theorem small_impossible (N W : OpenSquare) (n : LeftInput N) (t : TopInput W)
    (w : QuadrantData W) (same : N.side=W.side) (small : N.s≤N.c/3)
    (face : W.c-(63/50)*W.s≤W.loV)
    (axes : upper N N.c N.s≤lower W N.c N.s ∨
      upper N W.c W.s≤lower W W.c W.s) : False := by
  have coeff := coefficients N W n w
  rcases axes with leftAxis | topAxis
  · have support := lower_support_strict N W n t w same face
    have targetBound := target_low N W n w (by linarith only [small,n.cosine])
    have marker := (strict_bounds N _ _ N.c N.s N.unit_normal n.marker).2
    have first := mul_nonneg w.sine.le (sub_nonneg.mpr leftAxis)
    have last := mul_pos w.sine
      (show 0<upper N N.c N.s-((13/50)*N.c+N.s) by
        linarith only [marker,small,n.cosine])
    linarith only [support,targetBound,first,last]
  · have wall := ShallowTop.top_wall_faces W t w
    have formula := upper_wall_normal N W n w
    have first := mul_pos coeff.1 (sub_pos.mpr n.marker.2.1)
    have last := mul_pos coeff.2 (sub_pos.mpr n.high.2.2.2)
    have Q : alpha N W*((13/20)*N.c+(7/20)*N.s)+
        beta N W*(N.c-(1/4)*N.s)<upper N W.c W.s := by
      nlinarith only [first,last,formula]
    rw [(ownU W).1] at topAxis
    have markerWeight := mul_pos w.sine (sub_pos.mpr Q)
    have separator := mul_nonneg w.sine.le (sub_nonneg.mpr topAxis)
    have lowerFace := mul_nonneg w.cosine (sub_nonneg.mpr face)
    have extra := mul_pos (show 0<W.side-1 by linarith only [n.side,same])
      (show 0<W.c+W.s by linarith only [w.cosine,w.sine])
    have residual := small_residual N.c N.s W.c W.s n.cosine n.sine N.unit_normal
      n.angleLower small w.cosine w.sine W.unit_normal w.slope
    have identity : W.s*(alpha N W*((13/20)*N.c+(7/20)*N.s)+
          beta N W*(N.c-(1/4)*N.s))+W.c^2-(63/50)*W.c*W.s+W.c+W.s-2=
        W.c+W.s-1+W.s^2*((2/5)*N.c*N.s-(13/20)*N.s^2)-
          W.c*W.s*(61/100+(2/5)*N.s^2+(13/20)*N.c*N.s) := by
      dsimp only [alpha,beta,ShallowTop.alpha,ShallowTop.gamma]
      linear_combination W.s*((13/20)*W.c+W.s)*N.unit_normal+W.unit_normal
    nlinarith only [wall,markerWeight,separator,lowerFace,extra,residual,identity]

end N12Compact.Completion.OtherCases.C976LeftTop
