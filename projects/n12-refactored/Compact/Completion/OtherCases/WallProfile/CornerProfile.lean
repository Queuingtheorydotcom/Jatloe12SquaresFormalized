import Compact.Completion.OtherCases.WallProfile.SupportGeometry
import Compact.Completion.C1092.WallProfileScalars
import Mathlib.Tactic.LinearCombination

/-! The full corner support profile from the actual corner's walls and
one excluded upper point. This is Theorem6 of C1092-DIRECT-WALL-POINT.
All orientations and all first-quadrant target directions are included. -/
namespace N12Compact.Completion.OtherCases.WallProfile
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
open C1092WallProfileScalars
set_option Elab.async false

private theorem kappa_complement (c s : ℝ) (cn : 0 ≤ c) (sn : 0 ≤ s)
    (unit : c^2+s^2=1) :
    1-(c+s)/(1+c) ≤ c/2 := by
  have cu : c ≤ 1 := by nlinarith only [unit,sq_nonneg s,sq_nonneg (c-1)]
  have cp : 0 < 1+c := by linarith only [cn]
  have sp : 0 < 1+s := by linarith only [sn]
  have bracket := add_nonneg (sub_nonneg.mpr cu)
    (mul_nonneg sn (show 0 ≤ 1+c by linarith only [cn]))
  have product := mul_nonneg cn bracket
  have identity :
      (1+s)*(c*(1+c)-2*(1-s))=c*(1-c+s*(1+c)) := by
    linear_combination 2*unit
  have mid : 0 ≤ c*(1+c)-2*(1-s) :=
    nonneg_of_mul_nonneg_right (by rw [identity]; exact product) sp
  have scaled : (1+c)*(c/2-(1-(c+s)/(1+c))) =
      (c*(1+c)-2*(1-s))/2 := by
    field_simp [cp.ne']
    ring
  have nonnegative : 0 ≤ (1+c)*(c/2-(1-(c+s)/(1+c))) := by
    rw [scaled]
    exact div_nonneg mid (by norm_num)
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right nonnegative cp)

private theorem in_positive_frame (q : OpenSquare) (c s : ℝ)
    (side : 1 < q.side) (cp : 0 < q.c) (tn : 0 ≤ q.s)
    (wall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (anchor : q.Inside 1 1) (missing : ¬q.Inside 1 (3/2))
    (cn : 0 ≤ c) (sn : 0 ≤ s) (unit : c^2+s^2=1) :
    q.side*profile c s ≤ upper q c (-s) := by
  have walls := positive_frame_wall_bounds q cp.le tn wall
  have xwall : 0 ≤ q.c*q.loU-q.s*(q.loV+q.side) := by
    dsimp [centerX] at walls
    nlinarith only [walls.1]
  have rOne : q.c ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.s,sq_nonneg (q.c-1)]
  have tOne : q.s ≤ 1 := by
    nlinarith only [q.unit_normal,sq_nonneg q.c,sq_nonneg (q.s-1)]
  have lowU : q.loU < q.c+(3/2)*q.s := by
    simp only [OpenSquare.Inside,InBands,mul_one] at anchor
    linarith only [anchor.1,tn]
  have lowV : q.loV < -q.s+(3/2)*q.c := by
    simp only [OpenSquare.Inside,InBands,mul_one] at anchor
    linarith only [anchor.2.2.1,cp]
  have exit : q.loU+q.side ≤ q.c+(3/2)*q.s ∨
      q.loV+q.side ≤ -q.s+(3/2)*q.c := by
    by_cases first : q.loU+q.side ≤ q.c+(3/2)*q.s
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro highV
      apply missing
      simp only [OpenSquare.Inside,InBands,mul_one]
      have highU := lt_of_not_ge first
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lowU,highU,lowV,highV]
  let F := profile c s
  let S := upper q c (-s)
  change q.side*F ≤ S
  by_cases axis : q.s=0
  · have rAxis : q.c=1 := by nlinarith only [q.unit_normal,axis,cp]
    have lower : 0 ≤ q.loU := by
      simpa only [axis,rAxis,mul_one,one_mul,mul_zero,zero_mul,sub_zero] using xwall
    have upperV : q.loV+q.side ≤ 3/2 := by
      rcases exit with first | second
      · exfalso
        have hi := anchor.2.1
        simp only [axis,rAxis,mul_one,mul_zero,add_zero] at first hi
        linarith only [first,hi]
      · simpa only [axis,rAxis,neg_zero,mul_one,zero_add] using second
    have formula : S=c*q.loU-s*q.loV+q.side*c := by
      have h := downward_upper q c s cp.le tn cn sn
      simp only [rAxis,axis,mul_one,mul_zero,sub_zero,add_zero,zero_add,max_eq_left cn] at h
      exact h
    have cornerEnvelope : F ≤ c-s/2 := by
      have h := envelope c s 1 0 cn sn (by norm_num) (by norm_num) unit (by norm_num)
      simp only [mul_zero,zero_div,mul_one,add_zero,zero_add,sub_zero,max_eq_left cn] at h
      convert h using 1 <;> dsimp [F] <;> ring
    have lowerWeight := mul_nonneg cn lower
    have upperWeight := mul_nonneg sn (sub_nonneg.mpr upperV)
    have extra := mul_nonneg (show 0 ≤ (3/2)*s by linarith only [sn])
      (sub_nonneg.mpr side.le)
    have bound : q.side*(c-s/2) ≤ S := by
      nlinarith only [formula,lowerWeight,upperWeight,extra]
    exact (mul_le_mul_of_nonneg_left cornerEnvelope q.side_pos.le).trans bound
  · have tp : 0 < q.s := lt_of_le_of_ne tn (Ne.symm axis)
    let τ := half q.c q.s
    let d := c*q.c-s*q.s
    let e := c*q.s+s*q.c
    let G := e+max d 0+s*τ-(3/2)*s
    have tauData := quarter_data q.c q.s cp.le tn q.unit_normal
    have tauNonnegative : 0 ≤ τ := tauData.1
    have tauUpper : τ ≤ 1 := tauData.2.1
    have tauScale : τ*(1+q.c)=q.s := tauData.2.2.1
    have tauRelation : q.s*τ=1-q.c := by
      have scale := congrArg (fun z : ℝ => q.s*z) tauScale
      dsimp at scale
      have zero : (1+q.c)*(q.s*τ-(1-q.c))=0 := by
        nlinarith only [scale,q.unit_normal]
      exact sub_eq_zero.mp ((mul_eq_zero.mp zero).resolve_left
        (show 1+q.c ≠ 0 by linarith only [cp]))
    have en : 0 ≤ e := add_nonneg (mul_nonneg cn tn) (mul_nonneg sn cp.le)
    have support : S=d*q.loU-e*q.loV+q.side*max d 0 :=
      downward_upper q c s cp.le tn cn sn
    have scalar : F ≤ G := by
      convert envelope c s q.c q.s cn sn cp.le tn unit q.unit_normal using 1 <;>
        dsimp only [F,G,d,e,τ,half] <;> ring
    have finish (bound : q.side*G ≤ S) : q.side*F ≤ S :=
      (mul_le_mul_of_nonneg_left scalar q.side_pos.le).trans bound
    rcases exit with first | second
    · apply finish
      have weightedWall := mul_nonneg en xwall
      have weightedFace := mul_nonneg sn (sub_nonneg.mpr first)
      have extra := mul_nonneg
        (mul_nonneg (sub_nonneg.mpr side.le) sn)
        (show 0 ≤ q.c+(3/2)*q.s by linarith only [cp,tn])
      have identity : q.s*(S-q.side*G) =
          e*(q.c*q.loU-q.s*(q.loV+q.side))+
          s*(q.c+(3/2)*q.s-(q.loU+q.side))+
          (q.side-1)*s*(q.c+(3/2)*q.s) := by
        rw [support]
        dsimp only [G,d,e]
        linear_combination -s*q.loU*q.unit_normal-q.side*s*tauRelation
      have scaled : 0 ≤ q.s*(S-q.side*G) := by
        rw [identity]
        exact add_nonneg (add_nonneg weightedWall weightedFace) extra
      exact sub_nonneg.mp (nonneg_of_mul_nonneg_right scaled tp)
    · by_cases dn : 0 ≤ d
      · apply finish
        have weightedWall := mul_nonneg dn xwall
        have weightedFace := mul_nonneg sn (sub_nonneg.mpr second)
        have firstExtra := mul_nonneg sn tauNonnegative
        have lastExtra := mul_nonneg
          (mul_nonneg (mul_nonneg (sub_nonneg.mpr side.le) sn) cp.le)
          (show 0 ≤ 3/2-τ by linarith only [tauUpper])
        have identity : q.c*(S-q.side*G) =
            d*(q.c*q.loU-q.s*(q.loV+q.side))+
            s*(-q.s+(3/2)*q.c-(q.loV+q.side))+
            s*τ+(q.side-1)*s*q.c*(3/2-τ) := by
          rw [support,max_eq_left dn]
          dsimp only [G,d,e]
          rw [max_eq_left (show 0 ≤ c*q.c-s*q.s from dn)]
          linear_combination -s*(q.loV+q.side)*q.unit_normal-s*tauScale
        have scaled : 0 ≤ q.c*(S-q.side*G) := by
          rw [identity]
          exact add_nonneg (add_nonneg (add_nonneg weightedWall weightedFace) firstExtra) lastExtra
        exact sub_nonneg.mp (nonneg_of_mul_nonneg_right scaled cp)
      · have dp : d < 0 := lt_of_not_ge dn
        have support' : S=d*q.loU-e*q.loV := by
          rw [support,max_eq_right dp.le,mul_zero,add_zero]
        have aLow : q.loU < q.c+q.s := by
          simpa only [mul_one] using anchor.1
        have strictU := mul_pos (show 0 < -d by linarith only [dp])
          (sub_pos.mpr aLow)
        have weightedV := mul_nonneg en (sub_nonneg.mpr second)
        let L := c-s+(1-q.c/2)*e
        have identity :
            d*(q.c+q.s)+e*(q.s-(3/2)*q.c+q.side)=L+(q.side-1)*e := by
          dsimp only [d,e,L]
          linear_combination (c-s)*q.unit_normal
        have strictSupport : L+(q.side-1)*e < S := by
          have gap : S-(L+(q.side-1)*e) =
              (-d)*(q.c+q.s-q.loU)+e*(-q.s+(3/2)*q.c-(q.loV+q.side)) := by
            rw [support',←identity]
            ring
          have positive := add_pos_of_pos_of_nonneg strictU weightedV
          rw [←gap] at positive
          linarith only [positive]
        have eLower : c ≤ e := by
          have positive := mul_nonneg cp.le
            (show 0 ≤ s-d by linarith only [sn,dp])
          have identity : (1+q.s)*(e-c)=q.c*(s-d) := by
            dsimp only [e,d]
            linear_combination c*q.unit_normal
          have scaled : 0 ≤ (1+q.s)*(e-c) := by rw [identity]; exact positive
          exact sub_nonneg.mp (nonneg_of_mul_nonneg_right scaled
            (show 0 < 1+q.s by linarith only [tn]))
        have sOne : s ≤ 1 := by
          nlinarith only [unit,sq_nonneg c,sq_nonneg (s-1)]
        let κ := (c+s)/(1+c)
        have kapNonnegative : 0 ≤ κ :=
          div_nonneg (add_nonneg cn sn) (by linarith only [cn])
        have kapUpper : κ ≤ 1 :=
          (div_le_iff₀ (show 0 < 1+c by linarith only [cn])).mpr
            (by linarith only [sOne])
        have complement : 1-κ ≤ c/2 := kappa_complement c s cn sn unit
        have Fformula : F=c-s*κ := by dsimp only [F,κ,profile]; ring
        have firstWeight := mul_nonneg
          (show 0 ≤ 1-q.c/2 by linarith only [rOne]) (sub_nonneg.mpr eLower)
        have secondWeight := mul_nonneg (sub_nonneg.mpr rOne) cn
        have thirdWeight := mul_nonneg (sub_nonneg.mpr sOne) (sub_nonneg.mpr kapUpper)
        have LLower : F ≤ L := by
          dsimp only [L]
          nlinarith only [firstWeight,secondWeight,thirdWeight,complement,Fformula]
        have eF : F ≤ e := by
          have product := mul_nonneg sn kapNonnegative
          nlinarith only [eLower,Fformula,product]
        have extra := mul_nonneg (sub_nonneg.mpr side.le) (sub_nonneg.mpr eF)
        exact le_of_lt (by nlinarith only [strictSupport,LLower,extra])

/-- Full original geometric profile. First-quadrant containment supplies
the true wall supports, strict(1,1) supplies the lower bands, and the
excluded(1,1.5) supplies both possible upper faces. -/
theorem corner_profile (q : OpenSquare) (side : 1 < q.side)
    (wall : ∀ x y, q.Inside x y → 0 ≤ x ∧ 0 ≤ y)
    (anchor : q.Inside 1 1) (missing : ¬q.Inside 1 (3/2))
    (c s : ℝ) (cn : 0 ≤ c) (sn : 0 ≤ s) (unit : c^2+s^2=1) :
    q.side*profile c s ≤ upper q c (-s) := by
  obtain ⟨r,cp,tn,shape,inside,support⟩ := positive_frame q
  have rWall : ∀ x y, r.Inside x y → 0 ≤ x ∧ 0 ≤ y :=
    fun x y h => wall x y ((inside x y).mp h)
  have result := in_positive_frame r c s (by simpa only [shape] using side) cp tn rWall
    ((inside _ _).mpr anchor) (fun h => missing ((inside _ _).mp h)) cn sn unit
  simpa only [shape,support] using result

#print axioms corner_profile
end N12Compact.Completion.OtherCases.WallProfile

