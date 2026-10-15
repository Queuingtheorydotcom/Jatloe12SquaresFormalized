import Compact.Completion.OtherCases.C976NegativeTop.SeparatingAxes
import Compact.Completion.OtherCases.C976NegativeTop.QuadrantScalars

/-! Section 2: the genuine left point omitted by the top square forces
its lower-U face. Both signs of the relative-axis coefficient are kept. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

theorem left_face (N W : OpenSquare) (s : ℝ)
    (signed : N.s= -s) (side : 1<N.side) (sameSide : N.side=W.side)
    (cp : 0<N.c) (sp : 0<s) (order : s≤N.c)
    (Cp : 0<W.c) (Sn : 0≤W.s) (ratio : (2/3)*W.s≤W.c)
    (profile : Faces N s) (origin : W.Inside 0 0)
    (left : ¬W.Inside (-18/25) 0)
    (axes : upper W N.c N.s≤lower N N.c N.s ∨
      upper N (-W.s) W.c≤lower W (-W.s) W.c) :
    -(18/25)*W.c≤W.loU := by
  have o := origin
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,zero_add,add_zero] at o
  have bounds := quadrant_bounds W.c W.s Cp Sn W.unit_normal ratio
  have unit : N.c^2+s^2=1 := by simpa only [signed,neg_sq] using N.unit_normal
  have cu : N.c≤1 := by nlinarith only [unit,sq_nonneg s,cp]
  let d := N.c*W.c-s*W.s
  let k := N.c*W.s+s*W.c
  have kp : 0<k := by
    have first := mul_nonneg cp.le Sn
    have last := mul_pos sp Cp
    dsimp only [k]
    linarith only [first,last]
  have relative : d^2+k^2=1 := by
    dsimp only [d,k]
    calc
      _ = (N.c^2+s^2)*(W.c^2+W.s^2) := by ring
      _ = 1 := by rw [unit,W.unit_normal]; norm_num
  have ku : k≤1 := by nlinarith only [relative,sq_nonneg d,kp]
  apply le_of_not_gt
  intro below
  have topExit : W.loV+W.side≤(18/25)*W.s := by
    apply le_of_not_gt
    intro upper
    apply left
    simp only [OpenSquare.Inside,InBands,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [below,upper,o.2.1,o.2.2.1,Cp,Sn]
  have kUpper : W.loV< -(1-(3/4)*W.s) := by
    rw [←sameSide] at topExit
    linarith only [topExit,side,Sn]
  have upperW : upper W N.c N.s=
      d*W.loU-k*W.loV+W.side*max d 0 := by
    rw [signed]
    simpa only [d,k] using WallProfile.downward_upper W N.c s Cp.le Sn cp.le sp.le
  have upperN : upper N (-W.s) W.c=
      -k*N.loU+d*N.loV+N.side*max d 0 := by
    have alpha : (-W.s)*N.c+W.c*N.s= -k := by rw [signed]; dsimp only [k]; ring
    have beta : -(-W.s)*N.s+W.c*N.c=d := by rw [signed]; dsimp only [d]; ring
    rw [WallProfile.upper_in_bands,alpha,beta,
      abs_of_nonpos (by linarith only [kp])]
    by_cases dn : 0≤d
    · rw [abs_of_nonneg dn,max_eq_left dn]; ring
    · rw [abs_of_nonpos (le_of_not_ge dn),max_eq_right (le_of_not_ge dn)]; ring
  rcases axes with northAxis | topAxis
  · rw [(ownU N).1,upperW] at northAxis
    have remainder : 0≤d*W.loU+W.side*max d 0 := by
      by_cases dn : 0≤d
      · rw [max_eq_left dn]
        have product := mul_nonneg dn o.2.1.le
        nlinarith only [product]
      · rw [max_eq_right (le_of_not_ge dn)]
        have product := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge dn) o.1.le
        nlinarith only [product]
    have strict := mul_pos kp (show 0< -(1-(3/4)*W.s)-W.loV by
      linarith only [kUpper])
    have lower : k*(1-(3/4)*W.s)<N.loU := by
      nlinarith only [northAxis,remainder,strict]
    have margin := lower_exit_margin N.c s W.c W.s cp sp.le Cp Sn W.unit_normal ratio
    change min ((13/50)*N.c) ((37/50)*s)≤k*(1-(3/4)*W.s) at margin
    exact (not_lt_of_ge (le_trans margin lower.le)) (lt_min profile.elbowU profile.inwardU)
  · rw [(ownV W).1,upperN] at topAxis
    have remainder : 0≤d*N.loV+N.side*max d 0 := by
      by_cases dn : 0≤d
      · rw [max_eq_left dn]
        have upperPositive : 0<N.loV+N.side := by linarith only [profile.floor,side,cu]
        have product := mul_nonneg dn upperPositive.le
        nlinarith only [product]
      · rw [max_eq_right (le_of_not_ge dn)]
        have product := mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge dn) profile.lowerV.le
        nlinarith only [product]
    have strict := mul_pos kp (sub_pos.mpr profile.elbowU)
    have floor : -(13/50)*N.c*k<W.loV := by
      nlinarith only [topAxis,remainder,strict]
    have productBound : N.c*k≤1 :=
      le_trans (mul_le_mul_of_nonneg_right cu kp.le) (by simpa only [one_mul] using ku)
    nlinarith only [floor,kUpper,productBound,bounds.2.1]

#print axioms left_face
end N12Compact.Completion.OtherCases.C976NegativeTop
