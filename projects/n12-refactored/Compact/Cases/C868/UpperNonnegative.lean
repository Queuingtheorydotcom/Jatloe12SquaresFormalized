import Compact.Cases.C868.LowerNegative
import Compact.Cases.C868.UpperGapScalars

/-! The two genuine top omissions close the nonnegative merged-upper
sector.  All hypotheses concern the same two physical squares.  The top
points may have different owners; only their actual strict exclusion is
used here.  Every equality/contact alternative is retained. -/
namespace N12Compact.C868.UpperNonnegative
open S12 S12Pilot C977CornerCubic C977NegativeCorner FourSquareAnchors ABTransverse
set_option Elab.async false
noncomputable section

structure Input (A H : OpenSquare) : Prop where
  lowerNormal : Normal A.c (-A.s)
  upperNormal : Normal H.c H.s
  side : 1<A.side
  same : A.side=H.side
  marker : A.Inside (33/20) (33/20)
  nearBottom : A.Inside 2 (87/50)
  nearLeft : A.Inside (87/50) 2
  left : A.Inside (3/2) 2
  below : A.Inside 2 (3/2)
  northwest : H.Inside (33/20) (47/20)
  northeast : H.Inside (47/20) (47/20)
  center : H.Inside 2 2
  missingBottom : ¬A.Inside (8/5) 1
  missingLeft : ¬A.Inside 1 (8/5)
  missingTopLeft : ¬H.Inside (87/50) 3
  missingTopRight : ¬H.Inside (113/50) 3
  apart : ∀ x y,¬(A.Inside x y ∧ H.Inside x y)

/-- The lower square's actual G3 forces the merged square's lower face;
the two top omissions then force both possible upper-face alternatives. -/
theorem upper_faces (A H : OpenSquare) (h : Input A H) :
    9*H.c<35*H.s ∧
      H.loV+H.side≤3*H.c-(87/50)*H.s ∧
      (H.loV+H.side≤3*H.c-(113/50)*H.s ∨
        H.loU+H.side≤(113/50)*H.c+3*H.s) := by
  have bounds := normal_bounds h.upperNormal
  have cp : 0<H.c := by linarith only [bounds.1]
  have size : 1<H.side := by simpa only [←h.same] using h.side
  have lower : (87/50)*H.c+2*H.s≤H.loU := by
    apply le_of_not_gt
    intro low
    apply h.apart (87/50) 2
    refine ⟨h.nearLeft,?_,?_,?_,?_⟩
    · linarith only [low]
    · linarith only [h.center.2.1,cp]
    · linarith only [h.center.2.2.1,h.upperNormal.1]
    · linarith only [h.northwest.2.2.2,cp,h.upperNormal.1]
  have tilt : 9*H.c<35*H.s := by
    linarith only [lower,h.northwest.1]
  have topLeft : H.loV+H.side≤3*H.c-(87/50)*H.s := by
    apply le_of_not_gt
    intro high
    apply h.missingTopLeft
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [h.northwest.1,cp,h.upperNormal.1]
    · linarith only [lower,size,bounds.2.2.2.1]
    · linarith only [h.center.2.2.1,cp,h.upperNormal.1]
    · linarith only [high]
  refine ⟨tilt,topLeft,?_⟩
  by_cases topRight : H.loV+H.side≤3*H.c-(113/50)*H.s
  · exact Or.inl topRight
  · right
    apply le_of_not_gt
    intro high
    apply h.missingTopRight
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [h.center.1,cp,h.upperNormal.1]
    · linarith only [high]
    · linarith only [h.center.2.2.1,cp,h.upperNormal.2.1]
    · linarith only [topRight]

/-- The negative-lower/nonnegative-upper alternative is impossible with
the literal compulsory crosspoints and two separately foreign top points. -/
theorem impossible (A H : OpenSquare) (h : Input A H) : False := by
  let c := H.c
  let s := H.s
  let C := A.c
  let t := -A.s
  let a := A.side
  let U := H.loU-2*(H.c+H.s)
  let V := H.loV-2*(H.c-H.s)
  let v := A.loV+A.side-2*(A.c-A.s)
  let α := c*C-s*t
  let β := s*C+c*t
  have hn : Normal c s := h.upperNormal
  have ha : Normal C t := h.lowerNormal
  have hnBounds := normal_bounds hn
  have haBounds := normal_bounds ha
  have cp : 0<c := by linarith only [hnBounds.1]
  have Cp : 0<C := by linarith only [haBounds.1]
  have an : 0≤α := by
    have p := mul_nonneg (sub_nonneg.mpr hn.2.1) Cp.le
    have q := mul_nonneg hn.1 (sub_nonneg.mpr ha.2.1)
    dsimp [α]
    nlinarith only [p,q]
  have bn : 0≤β := add_nonneg (mul_nonneg hn.1 Cp.le) (mul_nonneg cp.le ha.1)
  have size : 1<a := h.side
  have Unegative : U<0 := by dsimp [U]; linarith only [h.center.1]
  have Vnegative : V<0 := by dsimp [V]; linarith only [h.center.2.2.1]
  have near : -(13/50)*t<v := by dsimp [t,v]; linarith only [h.nearLeft.2.2.2]
  have northwest : U< -(7/20)*c+(7/20)*s := by
    dsimp [U,c,s]; linarith only [h.northwest.1]
  have faces := upper_faces A H h
  have tilt : 9*c≤35*s := faces.1.le
  have topLeft : V+a≤c+(13/50)*s := by
    dsimp [V,a,c,s]
    rw [h.same]
    linarith only [faces.2.1]
  have topCases : V+a≤c-(13/50)*s ∨ U+a≤(13/50)*c+s := by
    dsimp [V,U,a,c,s]
    rw [h.same]
    rcases faces.2.2 with first | second
    · exact Or.inl (by linarith only [first])
    · exact Or.inr (by linarith only [second])
  have separation := LowerNegative.only_lower_normal A H h.lowerNormal h.upperNormal
    h.same h.side h.marker h.nearBottom h.nearLeft h.left h.below
    h.northwest h.northeast h.center h.missingBottom h.missingLeft h.apart
  have lowerFormula : lower H (-A.s) A.c=2*(C+t)+β*U+α*V := by
    have p : -A.s*H.c+A.c*H.s=β := by dsimp [β,c,s,C,t]; ring
    have q : -(-A.s)*H.s+A.c*H.c=α := by dsimp [α,c,s,C,t]; ring
    rw [lower_in_bands,p,q,abs_of_nonneg bn,abs_of_nonneg an]
    calc
      _ = 2*(C+t)*(c^2+s^2)+β*U+α*V := by dsimp [α,β,U,V,c,s,C,t]; ring
      _ = _ := by rw [hn.2.2]; ring
  have sep : v≤β*U+α*V := by rw [lowerFormula] at separation; dsimp [v,C,t]; linarith only [separation]
  have modes := LowerNegative.modes A h.lowerNormal h.side h.marker h.missingBottom h.missingLeft
  have localModes : a-t-(2/5)*C≤v ∨ (13*t<C) ∨ a-C-(2/5)*t≤v := by
    rcases modes with first | second | third
    · left; dsimp [a,t,C,v]; linarith only [first]
    · exact Or.inr (Or.inl second.2)
    · right; right; dsimp [a,t,C,v]; linarith only [third.2]
  rcases localModes with first | shallow | third
  · have span : t+(2/5)*C≤1 := by linarith only [haBounds.2.2.2.2.2,ha.2.1]
    have positive : 0<v := by linarith only [first,size,span]
    have p := mul_nonpos_of_nonneg_of_nonpos bn Unegative.le
    have q := mul_nonpos_of_nonneg_of_nonpos an Vnegative.le
    nlinarith only [positive,p,q,sep]
  · rcases topCases with upperV | upperU
    · let R := β*(-(7/20)*c+(7/20)*s)+α*(c-(13/50)*s-a)
      have p := mul_nonneg bn (sub_nonneg.mpr northwest.le)
      have q := mul_nonneg an (show 0≤c-(13/50)*s-a-V by linarith only [upperV])
      have bound : v≤R := by dsimp [R]; nlinarith only [sep,p,q]
      have margin := UpperGapScalars.third c s C t hn ha tilt shallow.le
      have identity : -(13/50)*t-R=
          C*(c-1+(61/100)*c*s+(13/20)*s^2)+
          t*(-s-13/25+(61/100)*c^2+(13/20)*c*s)+(a-1)*α := by
        calc
          _ = C*(c-1+(61/100)*c*s+(13/20)*s^2)+
              t*(-s-13/25+(61/100)*c^2+(13/20)*c*s)+(a-1)*α
              -(C+(13/50)*t)*(c^2+s^2-1) := by dsimp [R,α,β]; ring
          _ = _ := by rw [hn.2.2]; ring
      have extra := mul_nonneg (sub_nonneg.mpr size.le) an
      nlinarith only [near,bound,identity,margin,extra]
    · let R := β*((13/50)*c+s-a)+α*(c+(13/50)*s-a)
      have p := mul_nonneg bn (show 0≤(13/50)*c+s-a-U by linarith only [upperU])
      have q := mul_nonneg an (show 0≤c+(13/50)*s-a-V by linarith only [topLeft])
      have bound : v≤R := by dsimp [R]; nlinarith only [sep,p,q]
      have margin := UpperGapScalars.fourth c s C t hn ha shallow.le
      have identity : -(13/50)*t-R=
          C*(c+s-1-(13/25)*c*s)+t*(c-s-(13/50)*(c^2-s^2)-13/50)
          +(a-1)*(α+β) := by
        calc
          _ = C*(c+s-1-(13/25)*c*s)+t*(c-s-(13/50)*(c^2-s^2)-13/50)
              +(a-1)*(α+β)-C*(c^2+s^2-1) := by dsimp [R,α,β]; ring
          _ = _ := by rw [hn.2.2]; ring
      have extra := mul_nonneg (sub_nonneg.mpr size.le) (add_nonneg an bn)
      nlinarith only [near,bound,identity,margin,extra]
  · rcases topCases with upperV | upperU
    · let R := β*(-(7/20)*c+(7/20)*s)+α*(c-(13/50)*s-a)
      have p := mul_nonneg bn (sub_nonneg.mpr northwest.le)
      have q := mul_nonneg an (show 0≤c-(13/50)*s-a-V by linarith only [upperV])
      have bound : v≤R := by dsimp [R]; nlinarith only [sep,p,q]
      have margin := UpperGapScalars.first c s C t hn ha tilt
      have identity : a-C-(2/5)*t-R=
          1+C*(c-2+(61/100)*c*s+(13/20)*s^2)+
          t*(-s-33/50+(61/100)*c^2+(13/20)*c*s)+(a-1)*(1+α) := by
        calc
          _ = 1+C*(c-2+(61/100)*c*s+(13/20)*s^2)+
              t*(-s-33/50+(61/100)*c^2+(13/20)*c*s)+(a-1)*(1+α)
              -(C+(13/50)*t)*(c^2+s^2-1) := by dsimp [R,α,β]; ring
          _ = _ := by rw [hn.2.2]; ring
      have extra := mul_pos (sub_pos.mpr size) (show 0<1+α by linarith only [an])
      nlinarith only [third,bound,identity,margin,extra]
    · let R := β*((13/50)*c+s-a)+α*(c+(13/50)*s-a)
      have p := mul_nonneg bn (show 0≤(13/50)*c+s-a-U by linarith only [upperU])
      have q := mul_nonneg an (show 0≤c+(13/50)*s-a-V by linarith only [topLeft])
      have bound : v≤R := by dsimp [R]; nlinarith only [sep,p,q]
      have margin := UpperGapScalars.second c s C t hn ha
      have identity : a-C-(2/5)*t-R=
          1+C*(c+s-2-(13/25)*c*s)+
          t*(c-s-2/5-(13/50)*(c^2-s^2))+(a-1)*(1+α+β) := by
        calc
          _ = 1+C*(c+s-2-(13/25)*c*s)+
              t*(c-s-2/5-(13/50)*(c^2-s^2))+(a-1)*(1+α+β)
              -C*(c^2+s^2-1) := by dsimp [R,α,β]; ring
          _ = _ := by rw [hn.2.2]; ring
      have extra := mul_pos (sub_pos.mpr size) (show 0<1+α+β by linarith only [an,bn])
      nlinarith only [third,bound,identity,margin,extra]

#print axioms upper_faces
#print axioms impossible
end
end N12Compact.C868.UpperNonnegative
