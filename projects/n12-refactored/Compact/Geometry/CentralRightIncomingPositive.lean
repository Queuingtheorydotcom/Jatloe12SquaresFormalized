import Compact.Geometry.CentralRightCornerAlternatives
import Compact.Geometry.C977NegativeCorner
import Mathlib.Tactic.LinearCombination

/-! The other incoming central axis, with a nonnegative test direction
and a nonpositive southeast central frame. Full-square lower support
removes the upper-U escape of the actual inward wall point. -/
namespace N12Compact.CentralRightIncomingPositive

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner
set_option Elab.async false

private theorem margin {C S c t : ℝ} (an : Normal C S) (bn : Normal c t) :
    (C*c-S*t)*(3*c-2*t-1)+(C*t+S*c)*((33/20)*c+(47/20)*t)≤2*(C+S) := by
  have b := normal_bounds bn
  let dx := 1-c-(13/20)*t^2-(7/20)*c*t
  let dy := -(7/20)+(7/20)*t^2-(13/20)*c*t+t
  have dxIdentity : dx=(1-c)*((7/20)-(13/20)*c)-(7/20)*c*t := by
    dsimp [dx]
    linear_combination -(13/20)*bn.2.2
  have sumIdentity : dx+dy= -(c-t)*(1-(13/20)*c+(7/20)*t) := by
    dsimp [dx,dy]
    linear_combination -(13/20)*bn.2.2
  have first := mul_nonneg (sub_nonneg.mpr b.2.1)
    (show 0≤(13/20)*c-(7/20) by linarith only [b.1])
  have second := mul_nonneg (show 0≤c by linarith only [b.1]) bn.1
  have dxNonpos : dx≤0 := by nlinarith only [dxIdentity,first,second]
  have third := mul_nonneg (sub_nonneg.mpr bn.2.1)
    (show 0≤1-(13/20)*c+(7/20)*t by linarith only [b.2.1,bn.1])
  have sumNonpos : dx+dy≤0 := by nlinarith only [sumIdentity,third]
  have xWeight := mul_nonneg (sub_nonneg.mpr an.2.1)
    (show 0≤-dx by linarith only [dxNonpos])
  have sumWeight := mul_nonneg an.1 (show 0≤-(dx+dy) by linarith only [sumNonpos])
  have expression :
      (C*c-S*t)*(3*c-2*t-1)+(C*t+S*c)*((33/20)*c+(47/20)*t)-2*(C+S)=
      C*dx+S*dy := by
    dsimp [dx,dy]
    linear_combination (3*C+(33/20)*S)*bn.2.2
  nlinarith only [expression,xWeight,sumWeight]

/-- If this negative central square ends before the inward wall point
on U, its entire lower support in every positive canonical direction is
at most the corresponding support value of the container center. -/
theorem upper_u_bound (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1≤B.side) (marker : B.Inside (47/20) (33/20))
    (cap : B.loU+B.side≤3*B.c-2*t) : lower B C S≤2*(C+S) := by
  let K := C*B.c-S*t
  let H := C*t+S*B.c
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have cp : 0≤C := by linarith only [ab.1]
  have bp : 0≤B.c := by linarith only [bb.1]
  have first := mul_nonneg bp (sub_nonneg.mpr an.2.1)
  have second := mul_nonneg an.1 (sub_nonneg.mpr bn.2.1)
  have kNonneg : 0≤K := by dsimp [K]; nlinarith only [first,second]
  have hNonneg : 0≤H := by
    dsimp [H]
    exact add_nonneg (mul_nonneg cp bn.1) (mul_nonneg an.1 bp)
  have formula : lower B C S=K*B.loU+H*B.loV := by
    rw [lower_in_bands,signed]
    change _=K*B.loU+H*B.loV
    rw [show C*B.c+S*(-t)=K by dsimp [K]; ring,
      show -C*(-t)+S*B.c=H by dsimp [H]; ring,
      abs_of_nonneg kNonneg,abs_of_nonneg hNonneg]
    ring
  have along := mul_nonneg kNonneg
    (show 0≤3*B.c-2*t-1-B.loU by linarith only [cap,side])
  have across := mul_nonneg hNonneg
    (show 0≤(33/20)*B.c+(47/20)*t-B.loV by
      nlinarith only [marker.2.2.1,signed])
  have bound := margin an bn
  dsimp [K,H] at formula along across
  nlinarith only [formula,along,across,bound]

/-- In the genuine lower-V corner escape, the incoming A-owned axis
therefore forces the strict inward point itself. -/
theorem lower_escape_point (B : OpenSquare) (t : ℝ) {C S : ℝ}
    (an : Normal C S) (bn : Normal B.c t) (signed : B.s=-t)
    (side : 1<B.side) (marker : B.Inside (47/20) (33/20))
    (low : B.Inside 3 (87/50)) (escape : B.c+3*t≤B.loV)
    (incoming : 2*(C+S)<lower B C S) : B.Inside 3 2 := by
  by_contra missing
  have b := normal_bounds bn
  have cap : B.loU+B.side≤3*B.c-2*t := by
    apply le_of_not_gt
    intro high
    apply missing
    refine ⟨?_,?_,?_,?_⟩ <;>
      nlinarith only [marker.1,low.2.2.1,high,escape,side,signed,bn.1,bn.2.1,b.1,b.2.1]
  have bound := upper_u_bound B t an bn signed side.le marker cap
  linarith only [bound,incoming]

#print axioms upper_u_bound
#print axioms lower_escape_point
end N12Compact.CentralRightIncomingPositive
