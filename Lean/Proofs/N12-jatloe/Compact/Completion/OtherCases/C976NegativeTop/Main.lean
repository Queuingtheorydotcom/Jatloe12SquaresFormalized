import Compact.Completion.OtherCases.C976NegativeTop.LeftFace
import Compact.Completion.OtherCases.C976NegativeTop.NortheastScalars
import Compact.Completion.OtherCases.C976NegativeTop.TopScalars

/-! The continuous two-square Theorem 1 of
C976-NEGATIVE-NE-TOP-ENDING.md. This is a local theorem about the actual
northeast and top squares, not an assertion of the finite C976 entrance
or the separate left/top angle theorem. All excluded contacts remain weak. -/
namespace N12Compact.Completion.OtherCases.C976NegativeTop
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse
set_option Elab.async false

private theorem contrary_impossible (N W : OpenSquare) (s : ℝ)
    (signed : N.s= -s) (side : 1<N.side) (sameSide : N.side=W.side)
    (cp : 0<N.c) (sp : 0<s) (order : s≤N.c)
    (Cp : 0<W.c) (Sn : 0≤W.s) (ratio : (2/3)*W.s≤W.c)
    (marker : N.Inside (7/20) (-13/20)) (elbow : N.Inside (13/50) 0)
    (right : ¬N.Inside 1 (-11/25)) (alternative : Alternative N)
    (origin : W.Inside 0 0) (left : ¬W.Inside (-18/25) 0)
    (wall : W.s*(W.loU+W.side)+W.c*(W.loV+W.side)≤1)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) : False := by
  have missingOrigin : ¬N.Inside 0 0 := fun h => apart 0 0 ⟨h,origin⟩
  have profile := faces N s signed side cp sp order marker elbow missingOrigin right alternative
  have axes := separating_axes N W s signed cp sp Cp.le Sn sameSide
    elbow (alternative_anchor N alternative) origin apart
  have lFloor := left_face N W s signed side sameSide cp sp order Cp Sn ratio
    profile origin left axes
  have unit : N.c^2+s^2=1 := by simpa only [signed,neg_sq] using N.unit_normal
  let d := N.c*W.c-s*W.s
  let k := N.c*W.s+s*W.c
  have kp : 0<k := by
    have first := mul_nonneg cp.le Sn
    have last := mul_pos sp Cp
    dsimp only [k]
    linarith only [first,last]
  have supportW : upper W N.c N.s=
      d*(W.loU+W.side)-k*W.loV-W.side*min d 0 := by
    rw [signed,WallProfile.downward_upper W N.c s Cp.le Sn cp.le sp.le]
    change d*W.loU-k*W.loV+W.side*max d 0=
      d*(W.loU+W.side)-k*W.loV-W.side*min d 0
    by_cases dn : 0≤d
    · rw [max_eq_left dn,min_eq_right dn]; ring
    · rw [max_eq_right (le_of_not_ge dn),min_eq_left (le_of_not_ge dn)]; ring
  have supportN : upper N (-W.s) W.c=
      -k*N.loU+d*N.loV+N.side*max d 0 := by
    have alpha : (-W.s)*N.c+W.c*N.s= -k := by rw [signed]; dsimp only [k]; ring
    have beta : -(-W.s)*N.s+W.c*N.c=d := by rw [signed]; dsimp only [d]; ring
    rw [WallProfile.upper_in_bands,alpha,beta,
      abs_of_nonpos (by linarith only [kp])]
    by_cases dn : 0≤d
    · rw [abs_of_nonneg dn,max_eq_left dn]; ring
    · rw [abs_of_nonpos (le_of_not_ge dn),max_eq_right (le_of_not_ge dn)]; ring
  have jFloor : N.side-(18/25)*W.c≤W.loU+W.side := by
    linarith only [lFloor,sameSide]
  have wallBound : W.c*W.loV≤1-W.s*(W.loU+W.side)-W.c*N.side := by
    rw [←sameSide] at wall ⊢
    nlinarith only [wall]
  have topBound : W.c*W.loV≤1-N.side*(W.c+W.s)+(18/25)*W.c*W.s := by
    have weighted := mul_nonneg Sn (sub_nonneg.mpr jFloor)
    nlinarith only [wallBound,weighted]
  rcases axes with northAxis | topAxis
  · rw [(ownU N).1,supportW] at northAxis
    have first := mul_nonneg Cp.le (sub_nonneg.mpr northAxis)
    have second := mul_nonneg kp.le (sub_nonneg.mpr wallBound)
    have third := mul_nonneg cp.le (sub_nonneg.mpr jFloor)
    have fourth := mul_nonneg Cp.le (sub_nonneg.mpr profile.upperU)
    have cross : W.c*d+W.s*k=N.c := by
      dsimp only [d,k]
      linear_combination N.c*W.unit_normal
    have weightedCross := congrArg (fun z : ℝ => z*(W.loU+W.side)) cross
    let D := N.c+W.c*k-W.c*min d 0+W.c
    have coefficient : 0<D := by
      have minTerm := mul_nonpos_of_nonneg_of_nonpos Cp.le (min_le_right d 0)
      have positive := mul_pos Cp kp
      dsimp only [D]
      linarith only [cp,Cp,minTerm,positive]
    have necessary : N.side*D≤(43/25)*N.c*W.c+(11/25)*W.c*s+k := by
      rw [←sameSide] at first second third weightedCross
      dsimp only [D]
      nlinarith only [first,second,third,fourth,weightedCross]
    have margin := northeast_margin N.c s W.c W.s cp sp.le order unit Cp Sn W.unit_normal ratio
    have scaled := mul_pos Cp margin
    have identity :
        W.c*(1+N.c*((1-W.s)/W.c+W.s-43/25)-s*(36/25-W.c)-min d 0)=
        D-((43/25)*N.c*W.c+(11/25)*W.c*s+k) := by
      dsimp only [D,k]
      field_simp [ne_of_gt Cp]
      ring
    have strict := mul_pos (sub_pos.mpr side) coefficient
    change 0<W.c*(1+N.c*((1-W.s)/W.c+W.s-43/25)-s*(36/25-W.c)-min d 0) at scaled
    nlinarith only [necessary,strict,scaled,identity]
  · rw [(ownV W).1,supportN] at topAxis
    by_cases dn : 0≤d
    · rw [max_eq_left dn] at topAxis
      have topCase (v₀ : ℝ) (floor : v₀≤N.loV)
          (margin : 0<k*(1-N.c-(11/25)*s)+d*(1+v₀)+
            (1-(1-W.s)/W.c-(18/25)*W.s)) : False := by
        have first := mul_nonneg kp.le (sub_nonneg.mpr profile.upperU)
        have second := mul_nonneg dn (sub_nonneg.mpr floor)
        have lower : N.side*(k+d)-k*(N.c+(11/25)*s)+d*v₀≤W.loV := by
          nlinarith only [topAxis,first,second]
        have weighted := mul_nonneg Cp.le (sub_nonneg.mpr lower)
        let D := W.c*(k+d)+W.c+W.s
        have coefficient : 0<D := by
          have product := mul_pos Cp (show 0<k+d by linarith only [kp,dn])
          dsimp only [D]
          linarith only [product,Cp,Sn]
        have necessary : N.side*D≤1+(18/25)*W.c*W.s+
            W.c*k*(N.c+(11/25)*s)-W.c*d*v₀ := by
          dsimp only [D]
          nlinarith only [weighted,topBound]
        have scaled := mul_pos Cp margin
        have identity : W.c*(k*(1-N.c-(11/25)*s)+d*(1+v₀)+
            (1-(1-W.s)/W.c-(18/25)*W.s))=
            D-(1+(18/25)*W.c*W.s+W.c*k*(N.c+(11/25)*s)-W.c*d*v₀) := by
          dsimp only [D]
          field_simp [ne_of_gt Cp]
          ring
        have strict := mul_pos (sub_pos.mpr side) coefficient
        nlinarith only [necessary,scaled,identity,strict]
      rcases profile.alternatives with outer | mixed
      · exact topCase (-(37/50)*N.c) outer (by
          simpa only [d,k,neg_mul,sub_eq_add_neg] using top_outer_margin N.c s W.c W.s cp sp order unit
            Cp Sn W.unit_normal ratio dn)
      · exact topCase ((1/2)*s-N.c) mixed.1 (by
          simpa only [d,k,add_sub_assoc] using top_mixed_margin N.c s W.c W.s cp sp order unit
            Cp Sn W.unit_normal ratio mixed.2)
    · have dneg : d<0 := lt_of_not_ge dn
      rw [max_eq_right dneg.le] at topAxis
      have first := mul_nonneg kp.le (sub_nonneg.mpr profile.upperU)
      have second := mul_nonneg_of_nonpos_of_nonpos dneg.le profile.lowerV.le
      have lower : N.side*k-k*(N.c+(11/25)*s)≤W.loV := by
        nlinarith only [topAxis,first,second]
      have weighted := mul_nonneg Cp.le (sub_nonneg.mpr lower)
      let D := W.c*k+W.c+W.s
      have coefficient : 0<D := by dsimp only [D]; positivity
      have necessary : N.side*D≤1+(18/25)*W.c*W.s+W.c*k*(N.c+(11/25)*s) := by
        dsimp only [D]
        nlinarith only [weighted,topBound]
      have margin : 0<k*(1-N.c-(11/25)*s)+(1-(1-W.s)/W.c-(18/25)*W.s) := by
        simpa only [d,k] using top_negative_margin N.c s W.c W.s cp sp unit
          Cp Sn W.unit_normal ratio dneg
      have scaled := mul_pos Cp margin
      have identity : W.c*(k*(1-N.c-(11/25)*s)+(1-(1-W.s)/W.c-(18/25)*W.s))=
          D-(1+(18/25)*W.c*W.s+W.c*k*(N.c+(11/25)*s)) := by
        dsimp only [D]
        field_simp [ne_of_gt Cp]
        ring
      have strict := mul_pos (sub_pos.mpr side) coefficient
      nlinarith only [necessary,scaled,identity,strict]

/-- C976-NEGATIVE-NE-TOP-ENDING, Theorem 1. The conclusion is division
free and includes the strictly positive denominator needed for C/S<2/3. -/
theorem angle (N W : OpenSquare) (s : ℝ)
    (signed : N.s= -s) (side : 1<N.side) (sameSide : N.side=W.side)
    (cp : 0<N.c) (sp : 0<s) (order : s≤N.c)
    (Cn : 0≤W.c) (Sn : 0≤W.s)
    (marker : N.Inside (7/20) (-13/20)) (elbow : N.Inside (13/50) 0)
    (right : ¬N.Inside 1 (-11/25)) (alternative : Alternative N)
    (origin : W.Inside 0 0) (left : ¬W.Inside (-18/25) 0)
    (wall : W.s*(W.loU+W.side)+W.c*(W.loV+W.side)≤1)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) :
    0<W.s ∧ W.c<(2/3)*W.s := by
  have ratio : W.c<(2/3)*W.s := by
    apply lt_of_not_ge
    intro bad
    have Cp : 0<W.c := by
      apply lt_of_not_ge
      intro zero
      have cz : W.c=0 := le_antisymm zero Cn
      have sz : W.s=0 := by linarith only [bad,Sn,cz]
      have unit := W.unit_normal
      simp only [cz,sz] at unit
      norm_num at unit
    exact contrary_impossible N W s signed side sameSide cp sp order Cp Sn bad
      marker elbow right alternative origin left wall apart
  exact ⟨by linarith only [ratio,Cn],ratio⟩

/-- The same local theorem with the original geometric closure wall,
rather than its equivalent first-quadrant vertex support inequality. -/
theorem angle_of_closed_wall (N W : OpenSquare) (s : ℝ)
    (signed : N.s= -s) (side : 1<N.side) (sameSide : N.side=W.side)
    (cp : 0<N.c) (sp : 0<s) (order : s≤N.c)
    (Cn : 0≤W.c) (Sn : 0≤W.s)
    (marker : N.Inside (7/20) (-13/20)) (elbow : N.Inside (13/50) 0)
    (right : ¬N.Inside 1 (-11/25)) (alternative : Alternative N)
    (origin : W.Inside 0 0) (left : ¬W.Inside (-18/25) 0)
    (wall : ∀ x y,ClosedInside W x y → y≤1)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) :
    0<W.s ∧ W.c<(2/3)*W.s := by
  have vertex := WallProfile.vertex W (W.loU+W.side) (W.loV+W.side)
    ⟨by linarith only [W.side_pos],le_rfl⟩
    ⟨by linarith only [W.side_pos],le_rfl⟩
  exact angle N W s signed side sameSide cp sp order Cn Sn marker elbow right alternative
    origin left (wall _ _ vertex) apart

/-- Theorem 1 immediately excludes the nonnegative canonical top sign. -/
theorem nonnegative_top_impossible (N W : OpenSquare) (s : ℝ)
    (signed : N.s= -s) (side : 1<N.side) (sameSide : N.side=W.side)
    (cp : 0<N.c) (sp : 0<s) (order : s≤N.c)
    (Cp : 0<W.c) (Sn : 0≤W.s) (topOrder : W.s≤W.c)
    (marker : N.Inside (7/20) (-13/20)) (elbow : N.Inside (13/50) 0)
    (right : ¬N.Inside 1 (-11/25)) (alternative : Alternative N)
    (origin : W.Inside 0 0) (left : ¬W.Inside (-18/25) 0)
    (wall : ∀ x y,ClosedInside W x y → y≤1)
    (apart : ∀ x y,¬(N.Inside x y ∧ W.Inside x y)) : False := by
  have bound := angle_of_closed_wall N W s signed side sameSide cp sp order Cp.le Sn
    marker elbow right alternative origin left wall apart
  linarith only [bound.1,bound.2,topOrder]

#print axioms angle
#print axioms angle_of_closed_wall
#print axioms nonnegative_top_impossible
end N12Compact.Completion.OtherCases.C976NegativeTop
