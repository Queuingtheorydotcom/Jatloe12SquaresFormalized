import Compact.Geometry.CentralCenterPairIncoming
import Compact.Geometry.C977CornerCubic

/-! A positive center owner cannot receive the southeast neighbor on
that neighbor's transverse axis. The genuine northwest marker cap and
the actual lower paired-corner exclusion supply a uniform margin. -/
namespace N12Compact.CentralPositiveTransverse

open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C977CornerCubic C977NegativeCorner

theorem margin {C S c s : ℝ} (an : Normal C S) (bn : Normal c s) :
    0<1+(C*c+S*s)-
      (c*(27/20-(7/20)*S^2+(7/20)*C*S)+
        s*(1+(7/20)*S^2+(7/20)*C*S)) := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  let x := 27/20-C-(7/20)*S^2+(7/20)*C*S
  let y := 1-S+(7/20)*S^2+(7/20)*C*S
  have cp : 0≤C := by linarith only [ab.1]
  have product := mul_nonneg cp (show 0≤C+S by linarith only [cp,an.1])
  have xp : 0≤x := by
    dsimp [x]
    nlinarith only [product,ab.2.1,an.2.2]
  have orderProduct := mul_nonneg (sub_nonneg.mpr an.2.1)
    (show 0≤1-(7/20)*(C+S) by linarith only [ab.2.2.2.2.2])
  have orderIdentity : y-x=(C-S)*(1-(7/20)*(C+S)) := by
    dsimp [x,y]
    linear_combination (7/20)*an.2.2
  have order : x≤y := by clear_value x y; linarith only [orderIdentity,orderProduct]
  have arcProduct := mul_nonneg (sub_nonneg.mpr ab.2.2.2.2.1)
    (show 0≤1-(7/20)*(C+S+1) by linarith only [ab.2.2.2.2.2])
  have arc : 1+(7/10)*C*S≤C+S := by
    nlinarith only [arcProduct,an.2.2]
  have sum : x+y≤27/20 := by dsimp [x,y]; linarith only [arc]
  have reverse := mul_nonneg (sub_nonneg.mpr bn.2.1) (sub_nonneg.mpr order)
  have width := mul_nonneg (sub_nonneg.mpr bb.2.2.2.2.2)
    (show 0≤x+y by linarith only [xp,order])
  have weighted : c*x+s*y≤27/28 := by
    clear_value x y
    nlinarith only [reverse,width,sum]
  have identity : 1+(C*c+S*s)-
      (c*(27/20-(7/20)*S^2+(7/20)*C*S)+
        s*(1+(7/20)*S^2+(7/20)*C*S))=1-c*x-s*y := by
    dsimp [x,y]; ring
  linarith only [identity,weighted]

/-- The complete transverse selector is impossible. The corner miss is
supplied by the actual southeast paired owner in the original packing. -/
theorem impossible (A B : OpenSquare)
    (an : Normal A.c A.s) (bn : Normal B.c B.s)
    (same : A.side=B.side) (side : 1<A.side)
    (center : A.Inside 2 2)
    (cap : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (marker : B.Inside (47/20) (33/20)) (wall : B.Inside 3 (87/50))
    (missingCorner : ¬B.Inside 3 1)
    (separator : B.loV+B.side≤lower A (-B.s) B.c) : False := by
  have ab := normal_bounds an
  have bb := normal_bounds bn
  have ap : 0<A.c := by linarith only [ab.1]
  have bp : 0<B.c := by linarith only [bb.1]
  have floor : B.c-3*B.s≤B.loV := by
    apply le_of_not_gt
    intro low
    apply missingCorner
    refine ⟨?_,?_,by linarith only [low],?_⟩ <;>
      nlinarith only [marker.1,wall.2.1,marker.2.2.2,bp,bn.1,bn.2.1]
  let K := A.c*B.c+A.s*B.s
  let H := A.s*B.c-A.c*B.s
  have kp : 0<K := by
    have first := mul_pos ap bp
    have last := mul_nonneg an.1 bn.1
    dsimp [K]; linarith only [first,last]
  have support : lower A (-B.s) B.c≤2*H*(A.c+A.s)+K*A.loV := by
    rw [lower_in_bands]
    have first : (-B.s)*A.c+B.c*A.s=H := by dsimp [H]; ring
    have last : -(-B.s)*A.s+B.c*A.c=K := by dsimp [K]; ring
    rw [first,last,abs_of_nonneg kp.le]
    by_cases sign : 0≤H
    · rw [abs_of_nonneg sign]
      have bound := mul_nonneg sign (sub_nonneg.mpr
        (show A.loU≤2*(A.c+A.s) by linarith only [center.1]))
      clear_value K H
      nlinarith only [bound]
    · have negative : H≤0 := (lt_of_not_ge sign).le
      rw [abs_of_nonpos negative]
      have bound := mul_nonneg (neg_nonneg.mpr negative) (sub_nonneg.mpr
        (show 2*(A.c+A.s)≤A.loU+A.side by linarith only [center.2.1]))
      clear_value K H
      nlinarith only [bound]
  have across := mul_nonneg kp.le (sub_nonneg.mpr cap)
  have size := mul_pos (show 0<1+K by linarith only [kp]) (sub_pos.mpr side)
  have bound := margin an bn
  have identity :
      2*H*(A.c+A.s)+K*((47/20)*A.c-(33/20)*A.s)-B.c+3*B.s=
      B.c*(27/20-(7/20)*A.s^2+(7/20)*A.c*A.s)+
        B.s*(1+(7/20)*A.s^2+(7/20)*A.c*A.s) := by
    dsimp [K,H]
    linear_combination ((47/20)*B.c-2*B.s)*an.2.2
  rw [←same] at separator
  change 0 < 1 + K -
    (B.c*(27/20-(7/20)*A.s^2+(7/20)*A.c*A.s)+
      B.s*(1+(7/20)*A.s^2+(7/20)*A.c*A.s)) at bound
  clear_value K H
  nlinarith only [floor,separator,support,across,size,bound,identity]

/-- In this complete central orientation, the original three-mode SAT
classifier reduces to the two forward longitudinal axes. -/
theorem right_alternatives (A B : OpenSquare)
    (an : Normal A.c A.s) (bc : 0<B.c) (bn : |B.s|≤B.c)
    (same : A.side=B.side) (side : 1<A.side)
    (center : A.Inside 2 2) (low : A.Inside 2 (3/2))
    (right : A.Inside 2 (87/50))
    (cap : A.loV+A.side≤(47/20)*A.c-(33/20)*A.s)
    (marker : B.Inside (47/20) (33/20)) (wall : B.Inside 3 (87/50))
    (missingCorner : ¬B.Inside 3 1)
    (apart : ∀ x y, ¬(A.Inside x y ∧ B.Inside x y)) :
    A.loU+A.side≤lower B A.c A.s ∨ upper A B.c B.s≤B.loU := by
  have ab := normal_bounds an
  have axes := CentralCenterPairIncoming.right_alternatives A B
    (by linarith only [ab.1]) (by simpa only [abs_of_nonneg an.1] using an.2.1)
    bc bn same side center low right cap marker wall apart
  rcases axes with first | second | ⟨slope,transverse⟩
  · exact Or.inl first
  · exact Or.inr second
  · have positive : 0≤B.s := by linarith only [slope,bc]
    have normal : Normal B.c B.s :=
      ⟨positive,by simpa only [abs_of_nonneg positive] using bn,B.unit_normal⟩
    exact False.elim (impossible A B an normal same side center cap marker wall
      missingCorner transverse)

#print axioms margin
#print axioms impossible
#print axioms right_alternatives
end N12Compact.CentralPositiveTransverse
