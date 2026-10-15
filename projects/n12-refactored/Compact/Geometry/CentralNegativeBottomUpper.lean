import Compact.Geometry.CentralSteeperBottomReach
import Compact.Geometry.UpperRightNegativeTopBounds

/-! The upper-U escape of the actual bottom point cannot coexist with
the missing inward right point and an incoming positive central axis. -/
namespace N12Compact.CentralNegativeBottomUpper

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem margin {C S c t : ℝ} (an : Normal C S) (bn : Normal c t) :
    (C*c-S*t)*((13/5)*c-t-1)+(C*t+S*c)*(2*c+3*t-1)≤2*(C+S) := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have ct : c*t≤1/2 := by nlinarith only [bn.2.2,sq_nonneg (c-t)]
  have square : t^2≤1/2 := by
    have product := mul_nonneg (sub_nonneg.mpr bn.2.1)
      (show 0≤c+t by linarith only [bb.1,bn.1])
    nlinarith only [product,bn.2.2]
  have arc := UpperRightNegativeTopBounds.arc bn
  let X := 3/5-c-t+(2/5)*t^2+c*t
  let Y := -t^2+(2/5)*c*t-c+t
  have horizontal : X≤0 := by
    dsimp [X]
    nlinarith only [arc,square,ct]
  have diagonal : X+Y≤0 := by
    dsimp [X,Y]
    nlinarith only [bb.1,ct,sq_nonneg t]
  have first := mul_nonneg (sub_nonneg.mpr an.2.1) (neg_nonneg.mpr horizontal)
  have last := mul_nonneg an.1 (neg_nonneg.mpr diagonal)
  have identity : (C*c-S*t)*((13/5)*c-t-1)+(C*t+S*c)*(2*c+3*t-1)-
      2*(C+S)=C*X+S*Y := by
    dsimp [X,Y]
    linear_combination ((13/5)*C+2*S)*bn.2.2
  nlinarith only [first,last,identity]

theorem upper_u_impossible (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1≤B.side)
    (capU : B.loU+B.side≤(13/5)*B.c-t)
    (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*(C+S)<lower B C S) : False := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  let K := C*B.c-S*t
  let H := C*t+S*B.c
  have cp : 0≤C := by linarith only [ab.1]
  have bp : 0≤B.c := by linarith only [bb.1]
  have kp : 0≤K := by
    have first := mul_nonneg bp (sub_nonneg.mpr an.2.1)
    have last := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
    dsimp [K]; nlinarith only [first,last]
  have hp : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg cp bn.1) (mul_nonneg an.1 bp)
  have formula : lower B C S=K*B.loU+H*B.loV := by
    rw [lower_in_bands,signed]
    have u : C*B.c+S*(-t)=K := by dsimp [K]; ring
    have v : -C*(-t)+S*B.c=H := by dsimp [H]; ring
    rw [u,v,abs_of_nonneg kp,abs_of_nonneg hp]
    ring
  have first := mul_nonneg kp
    (show 0≤(13/5)*B.c-t-1-B.loU by linarith only [capU,side])
  have last := mul_nonneg hp
    (show 0≤2*B.c+3*t-1-B.loV by linarith only [capV,side])
  have bound := margin an bn
  dsimp [K,H] at formula first last
  nlinarith only [formula,first,last,bound,incoming]

/-- Both genuine missing-point escapes are considered. The upper face
has just been excluded, leaving the actual lower-V bound. -/
theorem lower_face (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1≤B.side) (marker : B.Inside (47/20) (33/20))
    (capV : B.loV+B.side≤2*B.c+3*t)
    (incoming : 2*(C+S)<lower B C S)
    (missing : ¬B.Inside (13/5) 1) : B.c+(13/5)*t≤B.loV := by
  have b := normal_bounds bn
  have m := (negative_bands B t _ _ signed).mp marker
  by_cases cap : B.loU+B.side≤(13/5)*B.c-t
  · exact False.elim (upper_u_impossible B t an bn signed side cap capV incoming)
  · apply le_of_not_gt
    intro low
    apply missing
    apply (negative_bands B t _ _ signed).mpr
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [m.1,m.2.2.2,cap,low,b.1,bn.1,bn.2.1]

end N12Compact.CentralNegativeBottomUpper
