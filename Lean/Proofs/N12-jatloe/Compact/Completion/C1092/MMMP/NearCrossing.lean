import Compact.Completion.C1092.MMMP.NearCrossingSupport

/-! The missing-center half-angle point with the compulsory .39 wall
endpoint retained. The endpoint first cuts the central angle; complete
support alternatives then cover every orientation of the same wall. -/
namespace N12Compact.C1092MMMPNearCrossing
open S12 S12Pilot ABTransverse C977CornerCubic
set_option Elab.async false

theorem point (C W : OpenSquare) (c s : ℝ)
    (cframe : C.c=c) (sframe : C.s=-s) (cn : Normal c s)
    (side : 1<C.side) (same : C.side=W.side) (lowerV : 0≤C.loV)
    (P : C.Inside 0 (13/50)) (Q : C.Inside (13/50) 0)
    (S : W.Inside (543/500) 0) (T : W.Inside 1 (13/50))
    (near : W.Inside 1 (39/100))
    (wall : ∀ x y, W.Inside x y → x≤2) (cut : 0≤centerY W)
    (apart : ∀ x y, ¬(C.Inside x y ∧ W.Inside x y)) :
    C.Inside (s/(1+c)) 1 := by
  classical
  have cb := normal_bounds cn
  have cp : 0<c := by linarith only [cb.1]
  have p := P
  have q := Q
  dsimp [OpenSquare.Inside,InBands] at p q
  rw [cframe,sframe] at p q
  have sp : 0<s := by nlinarith only [q.2.2.1,lowerV]
  let z := s/(1+c)
  have den : 0<1+c := by linarith only [cp]
  have zp : 0<z := div_pos sp den
  have angle : z*(1+c)=s := by dsimp [z]; field_simp [ne_of_gt den]
  have unitAngle : s*z=1-c := by
    dsimp [z]
    field_simp [ne_of_gt den]
    nlinarith only [cn.2.2]
  have clt : c<1 := by nlinarith only [cn.2.2,sq_pos_of_pos sp,cp]
  have zu : z<1/2 := by
    dsimp [z]
    apply (div_lt_iff₀ den).mpr
    linarith only [cn.2.1,clt]
  have crossing : C.loU < -z := by
    apply lt_of_not_ge
    intro failure
    let r0 := (1-z)^2/2
    let rho := max (39/100) r0
    have r0pos : 0<r0 := by
      dsimp [r0]
      exact div_pos (sq_pos_of_pos (by linarith only [zu])) (by norm_num)
    have r0upper : r0≤1/2 := by
      have product := mul_nonneg zp.le (show 0≤2-z by linarith only [zu])
      dsimp [r0]
      nlinarith only [product]
    have rhop : 0<rho := lt_of_lt_of_le (by norm_num : (0:ℝ)<39/100) (le_max_left _ _)
    have rhoupper : rho≤1/2 := max_le (by norm_num) r0upper
    have rho0 : r0≤rho := le_max_right _ _
    have ru : c-s*r0=1-z := by
      have times := congrArg (fun a : ℝ => a*z) unitAngle
      dsimp [r0] at ⊢
      nlinarith only [angle,unitAngle,times]
    have rv : s+c*r0=1-r0 := by
      have times := congrArg (fun a : ℝ => a*z) angle
      dsimp [r0] at ⊢
      nlinarith only [angle,unitAngle,times]
    have owned : C.Inside 1 rho := by
      dsimp [OpenSquare.Inside,InBands]
      rw [cframe,sframe]
      refine ⟨?_,?_,?_,?_⟩
      · have product := mul_nonneg sp.le (sub_nonneg.mpr rhoupper)
        nlinarith only [product,p.1,cn.2.1,sp]
      · have product := mul_nonneg sp.le (sub_nonneg.mpr rho0)
        nlinarith only [product,ru,failure,side]
      · have product := mul_pos cp rhop
        nlinarith only [product,q.2.2.1,sp]
      · by_cases compare : r0≤39/100
        · have eq : rho=39/100 := max_eq_left compare
          rw [eq]
          have short : s+(39/100)*c≤1 := by
            linarith only [cn.2.1,cb.2.2.2.2.2]
          nlinarith only [short,lowerV,side]
        · have eq : rho=r0 := max_eq_right (le_of_lt (lt_of_not_ge compare))
          rw [eq]
          nlinarith only [rv,r0pos,lowerV,side]
    have r0large : 39/100<r0 := by
      apply lt_of_not_ge
      intro compare
      have eq : rho=39/100 := max_eq_left compare
      rw [eq] at owned
      exact apart 1 (39/100) ⟨owned,near⟩
    have tiny : z<3/25 := by
      apply lt_of_not_ge
      intro failure
      have product := mul_nonneg (sub_nonneg.mpr failure)
        (show 0≤47/25-z by linarith only [zu])
      dsimp [r0] at r0large
      nlinarith only [r0large,product]
    have small : s≤1/4 := by
      have product := mul_nonneg zp.le (show 0≤1-c by linarith only [cb.2.1])
      nlinarith only [angle,product,tiny]
    have large : 13/50<rho := lt_of_lt_of_le (by norm_num : (13/50:ℝ)<39/100) (le_max_left _ _)
    exact C1092MMMPNearCrossingSupport.impossible C W c s z cframe sframe cn sp small zp.le zu.le
      angle unitAngle side same failure lowerV Q rho large owned S T wall cut apart
  have zlower : s/2≤z := by
    have product := mul_nonneg zp.le (show 0≤1-c by linarith only [cb.2.1])
    nlinarith only [angle,product]
  change C.Inside z 1
  dsimp [OpenSquare.Inside,InBands]
  rw [cframe,sframe]
  refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [crossing,angle,unitAngle,p.2.1,q.2.2.1,zlower,sp,lowerV,side,cb.2.2.2.1]

#print axioms point
end N12Compact.C1092MMMPNearCrossing
