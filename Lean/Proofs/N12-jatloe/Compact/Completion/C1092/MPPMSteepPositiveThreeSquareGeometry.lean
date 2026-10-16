import Compact.Completion.C1092.MPPMSteepPositiveThreeSquareData

/-! The simultaneous actual-side support caps and elimination of the
one actual boundary center in STEEP-POSITIVE-THREE-SQUARE-REDUCTION,
sections 3--4. At least one printed scalar mode must be strictly negative;
no scalar nonnegativity is assumed or asserted here. Source only. -/
namespace N12Compact.C1092MPPMSteepPositiveThreeSquare
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic C1092WholeSupports C1092MPPMCrosspointSupport
set_option Elab.async false
noncomputable section

private theorem dot_nonnegative {c s h r : ℝ} (cn : Normal c s) (bn : Quarter h r) :
    0≤c*h+s*r := by
  have cp : 0≤c := by linarith only [(normal_bounds cn).1]
  exact add_nonneg (mul_nonneg cp bn.cosine) (mul_nonneg cn.1 bn.sine)

theorem central_cap (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    lower C (-B.s) B.c≤FC C.c C.s B.c B.s-
      (C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|) := by
  have kn : 0≤kC C.c C.s B.c B.s := dot_nonnegative h.central bn
  have du : (-B.s)*C.c+B.c*C.s= -deltaC C.c C.s B.c B.s := by
    dsimp [deltaC]; ring
  have dv : -(-B.s)*C.s+B.c*C.c=kC C.c C.s B.c B.s := by
    dsimp [kC]; ring
  have upper := mul_le_mul_of_nonneg_left h.upperV kn
  by_cases order : 0≤deltaC C.c C.s B.c B.s
  · have formula := lower_np C (-B.s) B.c _ _ du dv
      (neg_nonpos.mpr order) kn
    have lower := mul_le_mul_of_nonneg_left h.lowerU order
    rw [FC,if_pos order,abs_of_nonneg order]
    nlinarith only [formula,lower,upper]
  · have order' : deltaC C.c C.s B.c B.s≤0 := (lt_of_not_ge order).le
    have formula := lower_nn C (-B.s) B.c _ _ du dv
      (neg_nonneg.mpr order') kn
    have face := mul_le_mul_of_nonneg_left h.upperU (neg_nonneg.mpr order')
    rw [FC,if_neg order,abs_of_nonpos order']
    nlinarith only [formula,face,upper]

theorem recipient_cap (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    lower E B.c B.s≤FE E.c E.s B.c B.s-
      (C.side-1)*kE E.c E.s B.c B.s := by
  have kn : 0≤kE E.c E.s B.c B.s := dot_nonnegative h.recipient bn
  have du : B.c*E.c+B.s*E.s=kE E.c E.s B.c B.s := by dsimp [kE]; ring
  have dv : -B.c*E.s+B.s*E.c=deltaE E.c E.s B.c B.s := by dsimp [deltaE]; ring
  have upper := mul_le_mul_of_nonneg_left h.upperE kn
  by_cases order : 0≤deltaE E.c E.s B.c B.s
  · have formula := lower_nn E B.c B.s _ _ du dv kn order
    have point := mul_le_mul_of_nonneg_left h.bottomE.2.2.1.le order
    rw [←h.sameE] at upper
    rw [FE,if_pos order]
    dsimp [E0]
    nlinarith only [formula,upper,point]
  · have order' : deltaE E.c E.s B.c B.s≤0 := (lt_of_not_ge order).le
    have formula := lower_pn E B.c B.s _ _ du dv kn order'
    have point := mul_nonpos_of_nonpos_of_nonneg order'
      (show 0≤E.loV+E.side+E.c/2 by linarith only [h.crosspointE.2.2.2])
    rw [←h.sameE] at upper formula point
    rw [FE,if_neg order]
    dsimp [E0]
    nlinarith only [formula,upper,point]

theorem floor_upper (B : OpenSquare) (bn : Quarter B.c B.s)
    (wall : ∀ x y,B.Inside x y→-2≤y) (nx ny : ℝ) (yn : 0≤ny) :
    nx*centerX B-2*ny+(B.side/2)*(ny*(B.c+B.s)+
      |nx*B.c+ny*B.s|+|-nx*B.s+ny*B.c|)≤upper B nx ny := by
  have floor := C1092ShallowBoundarySupport.bottom_center B wall
  simp only [C1092ShallowBoundarySupport.width0,abs_of_nonneg bn.cosine,
    abs_of_nonneg bn.sine] at floor
  have weight := mul_le_mul_of_nonneg_left floor yn
  dsimp [upper,supportRadius]
  nlinarith only [weight]

private theorem boundary_supports (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    (-C.s)*centerX B-2*C.c+(C.side/2)*(C.c*(B.c+B.s)+
      kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)≤upper B (-C.s) C.c ∧
    E.c*centerX B-2*E.s+(C.side/2)*(E.s*(B.c+B.s)+
      kE E.c E.s B.c B.s+|deltaE E.c E.s B.c B.s|)≤upper B E.c E.s ∧
    (-B.s)*centerX B-2*B.c+(C.side/2)*(B.c*(B.c+B.s)+1)≤upper B (-B.s) B.c ∧
    B.c*centerX B-2*B.s+(C.side/2)*(B.s*(B.c+B.s)+1)≤upper B B.c B.s := by
  have cn : 0≤C.c := by linarith only [(normal_bounds h.central).1]
  have kc : 0≤kC C.c C.s B.c B.s := dot_nonnegative h.central bn
  have ke : 0≤kE E.c E.s B.c B.s := dot_nonnegative h.recipient bn
  have first := floor_upper B bn h.wall (-C.s) C.c cn
  have second := floor_upper B bn h.wall E.c E.s h.recipient.1
  have third := floor_upper B bn h.wall (-B.s) B.c bn.cosine
  have fourth := floor_upper B bn h.wall B.c B.s bn.sine
  rw [show (-C.s)*B.c+C.c*B.s=deltaC C.c C.s B.c B.s by dsimp [deltaC]; ring,
    show -(-C.s)*B.s+C.c*B.c=kC C.c C.s B.c B.s by dsimp [kC]; ring,
    abs_of_nonneg kc,←h.sameB] at first
  rw [show E.c*B.c+E.s*B.s=kE E.c E.s B.c B.s by dsimp [kE],
    show -E.c*B.s+E.s*B.c= -deltaE E.c E.s B.c B.s by dsimp [deltaE]; ring,
    abs_neg,abs_of_nonneg ke,←h.sameB] at second
  rw [show (-B.s)*B.c+B.c*B.s=0 by ring,
    show -(-B.s)*B.s+B.c*B.c=1 by nlinarith only [bn.unit],←h.sameB] at third
  rw [show B.c*B.c+B.s*B.s=1 by nlinarith only [bn.unit],
    show -B.c*B.s+B.s*B.c=0 by ring,←h.sameB] at fourth
  refine ⟨?_,second,?_,?_⟩
  · convert first using 1 <;> ring
  · simpa only [abs_zero,abs_one,add_zero,zero_add] using third
  · simpa only [abs_zero,abs_one,add_zero,zero_add] using fourth

def H00 (c s d t h r : ℝ) : ℝ :=
  (k c s d t*(h+r)+d*(kC c s h r+|deltaC c s h r|)+
    s*(kE d t h r+|deltaE d t h r|))/2+d+s
def H01 (c s d t h r : ℝ) : ℝ :=
  (kC c s h r*(h+r)+h*(kC c s h r+|deltaC c s h r|)+s)/2+h+s*kE d t h r
def H10 (c s d t h r : ℝ) : ℝ :=
  (kE d t h r*(h+r)+d+r*(kE d t h r+|deltaE d t h r|))/2+
    d*(kC c s h r+|deltaC c s h r|)+r
def H11 (c s d t h r : ℝ) : ℝ :=
  h+r+h*(kC c s h r+|deltaC c s h r|)+r*kE d t h r

private theorem side_coefficients (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    0<H00 C.c C.s E.c E.s B.c B.s ∧
    0<H01 C.c C.s E.c E.s B.c B.s ∧
    0<H10 C.c C.s E.c E.s B.c B.s ∧
    0<H11 C.c C.s E.c E.s B.c B.s := by
  have cp : 0<C.c := by linarith only [(normal_bounds h.central).1]
  have sp : 0<C.s := by linarith only [h.steep]
  have dp : 0<E.c := by linarith only [(normal_bounds h.recipient).1]
  have tn := h.recipient.1
  have hn := bn.cosine
  have rn := bn.sine
  have kp : 0<k C.c C.s E.c E.s := by
    exact add_pos_of_pos_of_nonneg (mul_pos cp dp) (mul_nonneg sp.le tn)
  have kc : 0≤kC C.c C.s B.c B.s := dot_nonnegative h.central bn
  have ke : 0≤kE E.c E.s B.c B.s := dot_nonnegative h.recipient bn
  have sum : 0<B.c+B.s := by
    apply lt_of_not_ge
    intro no
    have hz : B.c=0 := by linarith only [hn,rn,no]
    have rz : B.s=0 := by linarith only [hn,rn,no]
    have unit := bn.unit
    rw [hz,rz] at unit
    norm_num at unit
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [H00]; positivity
  · dsimp [H01]; positivity
  · dsimp [H10]; positivity
  · have rest : 0≤B.c*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)+
        B.s*kE E.c E.s B.c B.s := by positivity
    dsimp [H11]
    linarith only [sum,rest]

theorem mode00 (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s)
    (csep : upper B (-C.s) C.c≤C.loV)
    (esep : upper B E.c E.s≤E.loU) : G00 C.c C.s E.c E.s B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap : C.loV≤C0 C.s-(C.side-1) := by dsimp [C0]; linarith only [h.upperV]
  have ecap : E.loU≤E0 E.c E.s-(C.side-1) := by
    dsimp [E0]; rw [h.sameE]; linarith only [h.upperE]
  have dp : 0≤E.c := by linarith only [(normal_bounds h.recipient).1]
  have sn := h.central.1
  have first := mul_nonpos_of_nonneg_of_nonpos dp
    (sub_nonpos.mpr ((supports.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos sn
    (sub_nonpos.mpr ((supports.2.1.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).1
  have identity : G00 C.c C.s E.c E.s B.c B.s+
      (C.side-1)*H00 C.c C.s E.c E.s B.c B.s=
      E.c*((-C.s)*centerX B-2*C.c+(C.side/2)*(C.c*(B.c+B.s)+
        kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)-(C0 C.s-(C.side-1)))+
      C.s*(E.c*centerX B-2*E.s+(C.side/2)*(E.s*(B.c+B.s)+
        kE E.c E.s B.c B.s+|deltaE E.c E.s B.c B.s|)-(E0 E.c E.s-(C.side-1))) := by
    dsimp [G00,H00,k]
    ring
  nlinarith only [first,last,strict,identity]

theorem mode01 (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s)
    (csep : upper B (-C.s) C.c≤C.loV)
    (esep : upper B B.c B.s≤lower E B.c B.s) : G01 C.c C.s E.c E.s B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap : C.loV≤C0 C.s-(C.side-1) := by dsimp [C0]; linarith only [h.upperV]
  have ecap := recipient_cap C E B h bn
  have first := mul_nonpos_of_nonneg_of_nonpos bn.cosine
    (sub_nonpos.mpr ((supports.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos h.central.1
    (sub_nonpos.mpr ((supports.2.2.2.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).2.1
  have identity : G01 C.c C.s E.c E.s B.c B.s+
      (C.side-1)*H01 C.c C.s E.c E.s B.c B.s=
      B.c*((-C.s)*centerX B-2*C.c+(C.side/2)*(C.c*(B.c+B.s)+
        kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)-(C0 C.s-(C.side-1)))+
      C.s*(B.c*centerX B-2*B.s+(C.side/2)*(B.s*(B.c+B.s)+1)-
        (FE E.c E.s B.c B.s-(C.side-1)*kE E.c E.s B.c B.s)) := by
    dsimp [G01,H01,kC]
    ring
  nlinarith only [first,last,strict,identity]

theorem mode10 (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s)
    (csep : upper B (-B.s) B.c≤lower C (-B.s) B.c)
    (esep : upper B E.c E.s≤E.loU) : G10 C.c C.s E.c E.s B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap := central_cap C E B h bn
  have ecap : E.loU≤E0 E.c E.s-(C.side-1) := by
    dsimp [E0]; rw [h.sameE]; linarith only [h.upperE]
  have dp : 0≤E.c := by linarith only [(normal_bounds h.recipient).1]
  have first := mul_nonpos_of_nonneg_of_nonpos dp
    (sub_nonpos.mpr ((supports.2.2.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos bn.sine
    (sub_nonpos.mpr ((supports.2.1.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).2.2.1
  have identity : G10 C.c C.s E.c E.s B.c B.s+
      (C.side-1)*H10 C.c C.s E.c E.s B.c B.s=
      E.c*((-B.s)*centerX B-2*B.c+(C.side/2)*(B.c*(B.c+B.s)+1)-
        (FC C.c C.s B.c B.s-(C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)))+
      B.s*(E.c*centerX B-2*E.s+(C.side/2)*(E.s*(B.c+B.s)+
        kE E.c E.s B.c B.s+|deltaE E.c E.s B.c B.s|)-(E0 E.c E.s-(C.side-1))) := by
    dsimp [G10,H10,kE]
    ring
  nlinarith only [first,last,strict,identity]

theorem mode11 (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s)
    (csep : upper B (-B.s) B.c≤lower C (-B.s) B.c)
    (esep : upper B B.c B.s≤lower E B.c B.s) : G11 C.c C.s E.c E.s B.c B.s<0 := by
  have supports := boundary_supports C E B h bn
  have ccap := central_cap C E B h bn
  have ecap := recipient_cap C E B h bn
  have first := mul_nonpos_of_nonneg_of_nonpos bn.cosine
    (sub_nonpos.mpr ((supports.2.2.1.trans csep).trans ccap))
  have last := mul_nonpos_of_nonneg_of_nonpos bn.sine
    (sub_nonpos.mpr ((supports.2.2.2.trans esep).trans ecap))
  have strict := mul_pos (sub_pos.mpr h.side) (side_coefficients C E B h bn).2.2.2
  have identity : G11 C.c C.s E.c E.s B.c B.s+
      (C.side-1)*H11 C.c C.s E.c E.s B.c B.s=
      B.c*((-B.s)*centerX B-2*B.c+(C.side/2)*(B.c*(B.c+B.s)+1)-
        (FC C.c C.s B.c B.s-(C.side-1)*(kC C.c C.s B.c B.s+|deltaC C.c C.s B.c B.s|)))+
      B.s*(B.c*centerX B-2*B.s+(C.side/2)*(B.s*(B.c+B.s)+1)-
        (FE E.c E.s B.c B.s-(C.side-1)*kE E.c E.s B.c B.s)) := by
    dsimp [G11,H11]
    linear_combination (2-C.side*(B.c+B.s)/2)*bn.unit
  nlinarith only [first,last,strict,identity]

/-- The exact geometric alternative at one fixed physical boundary
orientation. The same center and the same faces occur in both selected
separations. Actual side>1 supplies strictness at every weak contact. -/
theorem one_mode_negative_quarter (C E B : OpenSquare) (h : Input C E B)
    (bn : Quarter B.c B.s) :
    G00 C.c C.s E.c E.s B.c B.s<0 ∨ G01 C.c C.s E.c E.s B.c B.s<0 ∨
    G10 C.c C.s E.c E.s B.c B.s<0 ∨ G11 C.c C.s E.c E.s B.c B.s<0 := by
  rcases central_sources C E B h bn with current|boundaryC
  · rcases recipient_sources C E B h bn with recipient|boundaryE
    · exact Or.inl (mode00 C E B h bn current recipient)
    · exact Or.inr (Or.inl (mode01 C E B h bn current boundaryE))
  · rcases recipient_sources C E B h bn with recipient|boundaryE
    · exact Or.inr (Or.inr (Or.inl (mode10 C E B h bn boundaryC recipient)))
    · exact Or.inr (Or.inr (Or.inr (mode11 C E B h bn boundaryC boundaryE)))

/-- Every actual square admits a first-quadrant side reframe, including
both signs of its canonical angle and the two coordinate endpoints. The
returned orientation is of that same physical boundary square. -/
theorem one_mode_negative (C E B : OpenSquare) (h : Input C E B) :
    ∃ Q : OpenSquare,Q.side=B.side ∧
      (∀ x y,Q.Inside x y↔B.Inside x y) ∧ Quarter Q.c Q.s ∧
      (G00 C.c C.s E.c E.s Q.c Q.s<0 ∨ G01 C.c C.s E.c E.s Q.c Q.s<0 ∨
       G10 C.c C.s E.c E.s Q.c Q.s<0 ∨ G11 C.c C.s E.c E.s Q.c Q.s<0) := by
  obtain ⟨Q,qn,qr,side,_,_,inside⟩ := exists_positive_frame B
  have input : Input C E Q :=
    ⟨h.side,h.sameE,h.sameB.trans side.symm,h.central,h.recipient,h.steep,
      h.lowerU,h.upperU,h.upperV,h.markerC,h.ordinaryC,h.upperE,h.bottomE,h.crosspointE,
      (inside _ _).mpr h.markerB,(inside _ _).mpr h.outerB,(inside _ _).mpr h.originB,
      fun x y own => h.wall x y ((inside _ _).mp own),
      fun x y both => h.apartC x y ⟨(inside _ _).mp both.1,both.2⟩,
      fun x y both => h.apartE x y ⟨(inside _ _).mp both.1,both.2⟩⟩
  have quarter : Quarter Q.c Q.s := ⟨qn,qr,Q.unit_normal⟩
  exact ⟨Q,side,inside,quarter,one_mode_negative_quarter C E Q input quarter⟩

/-- The four explicit scalar inequalities needed by the geometric
reduction. This definition asserts no inequality and carries no pose or
support oracle; its proof is supplied by the separate scalar chapters. -/
def ModesNonnegative (c s d t : ℝ) : Prop := ∀ h r : ℝ,Quarter h r→
  0≤G00 c s d t h r ∧ 0≤G01 c s d t h r ∧
    0≤G10 c s d t h r ∧ 0≤G11 c s d t h r

theorem impossible_of_modes (C E B : OpenSquare) (h : Input C E B)
    (modes : ModesNonnegative C.c C.s E.c E.s) : False := by
  obtain ⟨Q,_,_,quarter,negative⟩ := one_mode_negative C E B h
  have positive := modes Q.c Q.s quarter
  rcases negative with a|b|c|d
  · exact (not_lt_of_ge positive.1) a
  · exact (not_lt_of_ge positive.2.1) b
  · exact (not_lt_of_ge positive.2.2.1) c
  · exact (not_lt_of_ge positive.2.2.2) d

end
#print axioms one_mode_negative_quarter
#print axioms one_mode_negative
#print axioms impossible_of_modes
end N12Compact.C1092MPPMSteepPositiveThreeSquare
