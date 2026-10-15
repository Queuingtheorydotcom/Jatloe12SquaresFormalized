import Compact.Completion.OtherCases.C983.C974WallSign
import Compact.Completion.OtherCases.C983.C974SingletonAngleScalars
import Compact.Completion.OtherCases.C983.C974LowerFace

/-! MISSING-CORNER-MIDPOINT §§1.2--1.4: the two actual square axes
exclude every K slope at least 3/4. This supplies the final angle premise
of the existing C974 three-square ending. Source translation, uncompiled. -/
namespace N12Compact.Completion.OtherCases.C983.C974MissingCorner
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem singleton_slope (K W : OpenSquare) (e : Input K W)
    (hp : 0<K.s) (orderK : K.s≤K.c) (tp : 0<W.s) (orderW : W.s≤W.c) :
    4*K.s<3*K.c := by
  let l := K.c
  let h := K.s
  let d := W.c
  let t := W.s
  let x := h/(1+l)
  have lp : 0<l := lt_of_lt_of_le hp orderK
  have dp : 0<d := lt_of_lt_of_le tp orderW
  have ku : l^2+h^2=1 := K.unit_normal
  have wu : d^2+t^2=1 := W.unit_normal
  have slope : 3*t<2*d := wall_positive_slope K W e dp tp.le orderW
  have cap := (singleton_positive_cap K W e lp hp.le).2
  by_contra no
  have steep : 3*l≤4*h := le_of_not_gt no
  have relative : 0<h*d-l*t := by
    have first := mul_nonneg dp.le (sub_nonneg.mpr steep)
    have last := mul_pos lp (sub_pos.mpr slope)
    have positive := mul_pos lp dp
    nlinarith only [first,last,positive]
  have obstruction := positive_support_obstruction K W e lp hp dp tp.le orderW cap relative.le
  have hu : h<1 := by nlinarith only [ku,sq_pos_of_pos lp,hp]
  have du : d≤1 := by nlinarith only [wu,sq_nonneg t,dp]
  have steepSquare := mul_nonneg (sub_nonneg.mpr steep) (show 0≤4*h+3*l by positivity)
  have hl : 3/5≤h := by nlinarith only [ku,steepSquare,hp]
  have lu : l≤4/5 := by nlinarith only [ku,steepSquare,lp]
  have relation : x*(1+l)=h := div_mul_cancel₀ _ (by positivity : (1+l:ℝ)≠0)
  have xl : 1/3≤x := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<1+l)).mpr
    linarith only [hl,lu]
  have first : 0≤1-d+(1-h)*(d*x-t) := by
    by_cases sign : 0≤d*x-t
    · have product := mul_nonneg (show 0≤1-h by linarith only [hu]) sign
      linarith only [du,product]
    · have sign' : d*x-t<0 := lt_of_not_ge sign
      have height := mul_nonneg (show 0≤h-3/5 by linarith only [hl]) (neg_nonneg.mpr sign'.le)
      have half := mul_nonneg dp.le (show 0≤x-1/3 by linarith only [xl])
      have projection : (13/15)*d+(2/5)*t<1 := by
        nlinarith only [wu,sq_nonneg ((2/5)*d-(13/15)*t)]
      nlinarith only [height,half,projection]
  have last : 0<(l*d+h*t)*(1-d)+(h*d-l*t)*(1-d/2)-x*(1-h) := by
    let A := d*(1-d/2)+t*(1-d)
    let B := d*(4-3*d-t)/2
    let G := (7/4)*d-(11/8)*d^2-(1/4)*d*t-t/4
    have Ap : 0<A := by
      have first := mul_pos dp (show 0<1-d/2 by linarith only [du])
      have last := mul_nonneg tp.le (show 0≤1-d by linarith only [du])
      dsimp only [A]
      linarith only [first,last]
    have identity : (l*d+h*t)*(1-d)+(h*d-l*t)*(1-d/2)=(h-l)*A+l*B := by
      dsimp only [A,B]
      ring
    have gIdentity : B-A/4=G := by dsimp only [A,B,G]; ring
    have gLower : 1/4<G := singleton_angle_G d t dp tp.le wu slope.le
    have weighted := mul_nonneg (show 0≤h-3*l/4 by linarith only [steep]) Ap.le
    have strict := mul_pos lp (show 0<G-1/4 by linarith only [gLower])
    have defect := quarter_defect l h x lp hp ku relation
    rw [identity]
    nlinarith only [weighted,strict,defect,gIdentity,
      show l*(B-A/4-G)=0 by rw [gIdentity]; ring]
  rcases obstruction with bad | bad
  · exact (not_lt_of_ge first) bad
  · exact (not_lt_of_ge last.le) bad

/-- Every premise of the already translated local ending now follows
from the raw input after physical positive-canonical reindexing. -/
theorem reduced_input (K W : OpenSquare) (e : Input K W)
    (hp : 0<K.s) (orderK : K.s≤K.c) (tp : 0<W.s) (orderW : W.s≤W.c) :
    C974LowerFace.Input K W := by
  have lp := lt_of_lt_of_le hp orderK
  have dp := lt_of_lt_of_le tp orderW
  have caps := wall_positive_caps K W e dp tp.le orderW
  refine
    { sideLarge := by simpa only [←e.sameSide] using e.sideLarge
      sameSide := e.sameSide
      kSine := hp
      kCanonical := orderK
      kSlope := singleton_slope K W e hp orderK tp orderW
      wSine := tp
      wCanonical := orderW
      wSlope := wall_positive_slope K W e dp tp.le orderW
      kA := e.a
      kS := e.s
      wO := e.o
      kUpperV := (singleton_positive_cap K W e lp hp.le).2
      kWall := singleton_wall K W e
      wUpperU := by linarith only [caps.1]
      wUpperV := by linarith only [caps.2]
      apart := e.apart }

end
#print axioms singleton_slope
#print axioms reduced_input
end N12Compact.Completion.OtherCases.C983.C974MissingCorner
