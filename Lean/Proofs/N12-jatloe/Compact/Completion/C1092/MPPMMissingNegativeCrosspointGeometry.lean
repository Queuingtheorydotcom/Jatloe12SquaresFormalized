import Compact.Completion.C1092.MPPMMissingNegativeCrosspointData

/-! Same-center elimination for the missing-negative successor.
The actual central upper-v face gives epsilon=43/500. Actual side>1
makes one of the four perturbed scalar modes strictly negative, including
every weak separating contact. No scalar positivity is assumed here.
Source only, uncompiled. -/
namespace N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
open S12 S12Pilot ThreeSquare C977ChainBridge ABTransverse C977CornerCubic
open C1092MPPMMissingNegativeCrosspointSupport
set_option Elab.async false
noncomputable section

private theorem boundary_supports (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    (-C.s)*centerX B-2*C.c+(C.side/2)*(C.c*(B.c+B.s)+
      kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)≤upper B (-C.s) C.c ∧
    (-E.s)*centerX B-2*E.c+(C.side/2)*(E.c*(B.c+B.s)+
      kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|)≤upper B (-E.s) E.c ∧
    (-B.s)*centerX B-2*B.c+(C.side/2)*(B.c*(B.c+B.s)+1)≤upper B (-B.s) B.c ∧
    B.c*centerX B-2*B.s+(C.side/2)*(B.s*(B.c+B.s)+1)≤upper B B.c B.s := by
  have cn : 0≤C.c := by linarith only [(normal_bounds h.central).1]
  have dn : 0≤E.c := by linarith only [(normal_bounds h.recipient.normal).1]
  have kc := central_dot C E B h bn
  have ke := recipient_dot C E B h bn
  have first := C1092MPPMSteepPositiveThreeSquare.floor_upper B bn h.wall (-C.s) C.c cn
  have second := C1092MPPMSteepPositiveThreeSquare.floor_upper B bn h.wall (-E.s) E.c dn
  have third := C1092MPPMSteepPositiveThreeSquare.floor_upper B bn h.wall (-B.s) B.c bn.cosine
  have fourth := C1092MPPMSteepPositiveThreeSquare.floor_upper B bn h.wall B.c B.s bn.sine
  rw [show (-C.s)*B.c+C.c*B.s=deltaC C.c C.s B.c B.s by dsimp [deltaC,C1092MPPMNegativeCrosspointSupport.deltaC]; ring,
    show -(-C.s)*B.s+C.c*B.c=kC C.c C.s B.c B.s by dsimp [kC,C1092MPPMNegativeCrosspointSupport.kC]; ring,
    abs_of_nonneg kc,←h.sameB] at first
  rw [show (-E.s)*B.c+E.c*B.s=kE E.c (-E.s) B.c B.s by dsimp [kE,C1092MPPMNegativeCrosspointSupport.kE],
    show -(-E.s)*B.s+E.c*B.c= -deltaE E.c (-E.s) B.c B.s by dsimp [deltaE,C1092MPPMNegativeCrosspointSupport.deltaE]; ring,
    abs_neg,abs_of_nonneg ke,←h.sameB] at second
  rw [show (-B.s)*B.c+B.c*B.s=0 by ring,
    show -(-B.s)*B.s+B.c*B.c=1 by nlinarith only [bn.unit],←h.sameB] at third
  rw [show B.c*B.c+B.s*B.s=1 by nlinarith only [bn.unit],
    show -B.c*B.s+B.s*B.c=0 by ring,←h.sameB] at fourth
  refine ⟨?_,second,?_,?_⟩
  · convert first using 1
    ring
  · simpa only [abs_zero,abs_one,zero_add,add_zero] using third
  · simpa only [abs_zero,abs_one,zero_add,add_zero] using fourth

def H00 (c s d t h r : ℝ) : ℝ := width c s d t h r/2+t+s
def H01 (c s d t h r : ℝ) : ℝ :=
  (kC c s h r*(h+r)+h*(kC c s h r+|deltaC c s h r|)+s)/2+h+
    s*(kE d t h r+|deltaE d t h r|)
def H10 (c s d t h r : ℝ) : ℝ :=
  (kE d t h r*(h+r)+t+r*(kE d t h r+|deltaE d t h r|))/2+
    t*(kC c s h r+|deltaC c s h r|)+r
def H11 (c s d t h r : ℝ) : ℝ :=
  h+r+h*(kC c s h r+|deltaC c s h r|)+r*(kE d t h r+|deltaE d t h r|)

private theorem side_coefficients (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    0<H00 C.c C.s E.c (-E.s) B.c B.s ∧ 0<H01 C.c C.s E.c (-E.s) B.c B.s ∧
    0<H10 C.c C.s E.c (-E.s) B.c B.s ∧ 0<H11 C.c C.s E.c (-E.s) B.c B.s := by
  have faces := recipient_faces E B h.recipient
  have cp : 0<C.c := by linarith only [(normal_bounds h.central).1]
  have dp : 0<E.c := by linarith only [(normal_bounds h.recipient.normal).1]
  have sp : 0<C.s := by linarith only [h.steep]
  have tp : 0< -E.s := by linarith only [faces.negative]
  have hn := bn.cosine
  have rn := bn.sine
  have kc := central_dot C E B h bn
  have ke := recipient_dot C E B h bn
  have ep : 0<ell C.c C.s E.c (-E.s) := by
    exact add_pos (mul_pos cp tp) (mul_pos sp dp)
  have sum : 0<B.c+B.s := by
    apply lt_of_not_ge
    intro no
    have hz : B.c=0 := by linarith only [no,hn,rn]
    have rz : B.s=0 := by linarith only [no,hn,rn]
    have unit := bn.unit
    rw [hz,rz] at unit
    norm_num at unit
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [H00,width,C1092MPPMNegativeCrosspointSupport.width]; positivity
  · dsimp [H01]; positivity
  · dsimp [H10]; positivity
  · have rest : 0≤B.c*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)+
        B.s*(kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|) := by positivity
    dsimp [H11]
    linarith only [sum,rest]

private theorem caps (C E B : OpenSquare) (h : Input C E B) :
    C.loV≤C0 C.s+(43/500)*C.s-(C.side-1) ∧
      E.loV≤E0 E.c (-E.s)-(C.side-1) := by
  have faces := recipient_faces E B h.recipient
  constructor
  · dsimp [C0,C1092MPPMNegativeCrosspointSupport.C0]; linarith only [h.upperV]
  · dsimp [E0]; linarith only [faces.upperV,h.sameE]

theorem mode00 (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s)
    (csep : upper B (-C.s) C.c≤C.loV) (esep : upper B (-E.s) E.c≤E.loV) :
    G00star (43/500) C.c C.s E.c (-E.s) B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have faces := caps C E B h
  have first := mul_nonpos_of_nonneg_of_nonpos h.recipient.normal.1
    (sub_nonpos.mpr ((supports.1.trans csep).trans faces.1))
  have last := mul_nonpos_of_nonneg_of_nonpos h.central.1
    (sub_nonpos.mpr ((supports.2.1.trans esep).trans faces.2))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).1
  have identity : G00star (43/500) C.c C.s E.c (-E.s) B.c B.s+
      (C.side-1)*H00 C.c C.s E.c (-E.s) B.c B.s=
      (-E.s)*((-C.s)*centerX B-2*C.c+(C.side/2)*(C.c*(B.c+B.s)+
        kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)-
          (C0 C.s+(43/500)*C.s-(C.side-1)))+
      C.s*((-E.s)*centerX B-2*E.c+(C.side/2)*(E.c*(B.c+B.s)+
        kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|)-
          (E0 E.c (-E.s)-(C.side-1))) := by
    dsimp [G00star,G00,H00,width,ell,C1092MPPMNegativeCrosspointSupport.width,C1092MPPMNegativeCrosspointSupport.ell]
    ring
  nlinarith only [first,last,strict,identity]

theorem mode01 (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s)
    (csep : upper B (-C.s) C.c≤C.loV) (esep : upper B B.c B.s≤lower E B.c B.s) :
    G01star (43/500) C.c C.s E.c (-E.s) B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap := (caps C E B h).1
  have ecap := recipient_cap C E B h bn
  have first := mul_nonpos_of_nonneg_of_nonpos bn.cosine
    (sub_nonpos.mpr ((supports.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos h.central.1
    (sub_nonpos.mpr ((supports.2.2.2.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).2.1
  have identity : G01star (43/500) C.c C.s E.c (-E.s) B.c B.s+
      (C.side-1)*H01 C.c C.s E.c (-E.s) B.c B.s=
      B.c*((-C.s)*centerX B-2*C.c+(C.side/2)*(C.c*(B.c+B.s)+
        kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)-
          (C0 C.s+(43/500)*C.s-(C.side-1)))+
      C.s*(B.c*centerX B-2*B.s+(C.side/2)*(B.s*(B.c+B.s)+1)-
        (FE E.c (-E.s) B.c B.s-
          (C.side-1)*(kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|))) := by
    dsimp [G01star,G01,H01,kC,C1092MPPMNegativeCrosspointSupport.kC]
    ring
  nlinarith only [first,last,strict,identity]

theorem mode10 (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s)
    (csep : upper B (-B.s) B.c≤lower C (-B.s) B.c) (esep : upper B (-E.s) E.c≤E.loV) :
    G10star (43/500) C.c C.s E.c (-E.s) B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap := central_cap C E B h bn
  have ecap := (caps C E B h).2
  have first := mul_nonpos_of_nonneg_of_nonpos h.recipient.normal.1
    (sub_nonpos.mpr ((supports.2.2.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos bn.sine
    (sub_nonpos.mpr ((supports.2.1.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).2.2.1
  have identity : G10star (43/500) C.c C.s E.c (-E.s) B.c B.s+
      (C.side-1)*H10 C.c C.s E.c (-E.s) B.c B.s=
      (-E.s)*((-B.s)*centerX B-2*B.c+(C.side/2)*(B.c*(B.c+B.s)+1)-
        (FC C.c C.s B.c B.s+(43/500)*C.s*kC C.c C.s B.c B.s-
          (C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)))+
      B.s*((-E.s)*centerX B-2*E.c+(C.side/2)*(E.c*(B.c+B.s)+
        kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|)-
          (E0 E.c (-E.s)-(C.side-1))) := by
    dsimp [G10star,G10,H10,kE,C1092MPPMNegativeCrosspointSupport.kE]
    ring
  nlinarith only [first,last,strict,identity]

theorem mode11 (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s)
    (csep : upper B (-B.s) B.c≤lower C (-B.s) B.c) (esep : upper B B.c B.s≤lower E B.c B.s) :
    G11star (43/500) C.c C.s E.c (-E.s) B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap := central_cap C E B h bn
  have ecap := recipient_cap C E B h bn
  have first := mul_nonpos_of_nonneg_of_nonpos bn.cosine
    (sub_nonpos.mpr ((supports.2.2.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos bn.sine
    (sub_nonpos.mpr ((supports.2.2.2.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).2.2.2
  have identity : G11star (43/500) C.c C.s E.c (-E.s) B.c B.s+
      (C.side-1)*H11 C.c C.s E.c (-E.s) B.c B.s=
      B.c*((-B.s)*centerX B-2*B.c+(C.side/2)*(B.c*(B.c+B.s)+1)-
        (FC C.c C.s B.c B.s+(43/500)*C.s*kC C.c C.s B.c B.s-
          (C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)))+
      B.s*(B.c*centerX B-2*B.s+(C.side/2)*(B.s*(B.c+B.s)+1)-
        (FE E.c (-E.s) B.c B.s-
          (C.side-1)*(kE E.c (-E.s) B.c B.s+|deltaE E.c (-E.s) B.c B.s|))) := by
    dsimp [G11star,G11,H11]
    linear_combination (2-C.side*(B.c+B.s)/2)*bn.unit
  nlinarith only [first,last,strict,identity]

def NegativeMode (c s d t h r : ℝ) : Prop :=
  G00star (43/500) c s d t h r<0 ∨ G01star (43/500) c s d t h r<0 ∨
    G10star (43/500) c s d t h r<0 ∨ G11star (43/500) c s d t h r<0

theorem one_mode_negative_quarter (C E B : OpenSquare) (h : Input C E B) (bn : Quarter B.c B.s) :
    NegativeMode C.c C.s E.c (-E.s) B.c B.s := by
  rcases central_sources C E B h bn with current|boundaryC
  · rcases recipient_sources C E B h bn with recipient|boundaryE
    · exact Or.inl (mode00 C E B h bn current recipient)
    · exact Or.inr (Or.inl (mode01 C E B h bn current boundaryE))
  · rcases recipient_sources C E B h bn with recipient|boundaryE
    · exact Or.inr (Or.inr (Or.inl (mode10 C E B h bn boundaryC recipient)))
    · exact Or.inr (Or.inr (Or.inr (mode11 C E B h bn boundaryC boundaryE)))

theorem one_mode_negative (C E B : OpenSquare) (h : Input C E B) :
    ∃ Q : OpenSquare,Q.side=B.side ∧ (∀ x y,Q.Inside x y↔B.Inside x y) ∧
      Quarter Q.c Q.s ∧ NegativeMode C.c C.s E.c (-E.s) Q.c Q.s := by
  obtain ⟨Q,qn,qr,side,_,_,inside⟩ := exists_positive_frame B
  have recipient : RecipientInput E Q :=
    ⟨h.recipient.side,h.recipient.normal,h.recipient.marker,h.recipient.ordinaryP,
      h.recipient.ordinaryG,h.recipient.halfpoint,h.recipient.corner,h.recipient.forward,
      h.recipient.bar,(inside _ _).mpr h.recipient.originB,
      fun x y both => h.recipient.apart x y ⟨(inside _ _).mp both.1,both.2⟩⟩
  have input : Input C E Q :=
    ⟨h.side,h.sameE,h.sameB.trans side.symm,h.central,h.steep,h.lowerU,h.upperU,h.upperV,
      h.markerC,h.ordinaryC,recipient,(inside _ _).mpr h.markerB,(inside _ _).mpr h.outerB,
      fun x y own => h.wall x y ((inside _ _).mp own),
      fun x y both => h.apartC x y ⟨(inside _ _).mp both.1,both.2⟩⟩
  have quarter : Quarter Q.c Q.s := ⟨qn,qr,Q.unit_normal⟩
  exact ⟨Q,side,inside,quarter,one_mode_negative_quarter C E Q input quarter⟩

def ModesNonnegative (c s d t : ℝ) : Prop := ∀ h r : ℝ,Quarter h r→
  0≤G00star (43/500) c s d t h r ∧ 0≤G01star (43/500) c s d t h r ∧
    0≤G10star (43/500) c s d t h r ∧ 0≤G11star (43/500) c s d t h r

theorem impossible_of_modes (C E B : OpenSquare) (h : Input C E B)
    (modes : ModesNonnegative C.c C.s E.c (-E.s)) : False := by
  obtain ⟨Q,_,_,quarter,negative⟩ := one_mode_negative C E B h
  have positive := modes Q.c Q.s quarter
  rcases negative with a|b|c|d
  · exact (not_lt_of_ge positive.1) a
  · exact (not_lt_of_ge positive.2.1) b
  · exact (not_lt_of_ge positive.2.2.1) c
  · exact (not_lt_of_ge positive.2.2.2) d

end
#print axioms one_mode_negative
#print axioms impossible_of_modes
end N12Compact.C1092MPPMMissingNegativeCrosspointGeometry
