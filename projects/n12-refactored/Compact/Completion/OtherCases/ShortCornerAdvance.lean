import Compact.Completion.C981.CornerAdvance

/-! The exact shorter corner reach with (p,q,r)=(.2,.6,.22).
Only the actual upper wall and the two genuine foreign points are used. -/
namespace N12Compact.Completion.OtherCases.ShortCornerAdvance
open S12 S12Pilot
set_option Elab.async false

private theorem positive (q : OpenSquare) (side : 1<q.side)
    (cp : 0<q.c) (sn : 0≤q.s)
    (wall : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1)
    (origin : q.Inside 0 0) (missingLeft : ¬q.Inside (-(3/5)) 0)
    (missingBelow : ¬q.Inside 0 (-(1/5))) : q.Inside (11/50) 0 := by
  have cu : q.c≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.s,cp]
  have su : q.s≤1 := by nlinarith only [q.unit_normal,sq_nonneg q.c,sn]
  have cross := mul_nonneg cp.le sn
  have sumLow : 1≤q.c+q.s := by nlinarith only [q.unit_normal,cross,cp,sn]
  have sumHigh : q.c+q.s≤10/7 := by
    nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s),cp,sn]
  have product := mul_nonneg (sub_nonneg.mpr sumLow) (sub_nonneg.mpr sumHigh)
  have arc : 1+(41/50)*q.c*q.s≤q.c+q.s := by
    nlinarith only [product,q.unit_normal,cross]
  have fHighU : -(3/5)*q.c<q.loU+q.side := by linarith only [origin.2.1,cp]
  have fLowV : q.loV<(3/5)*q.s := by linarith only [origin.2.2.1,sn]
  have exits : -(3/5)*q.c≤q.loU ∨ q.loV+q.side≤(3/5)*q.s := by
    by_cases first : -(3/5)*q.c≤q.loU
    · exact Or.inl first
    · right
      apply le_of_not_gt
      intro high
      apply missingLeft
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [first,fHighU,fLowV,high]
  have uLow : q.loU<(11/50)*q.c := by linarith only [origin.1,cp]
  have vHigh : -(11/50)*q.s<q.loV+q.side := by linarith only [origin.2.2.2,sn]
  rcases exits with fU | fV
  · have uHigh : (11/50)*q.c<q.loU+q.side := by linarith only [fU,side,cu]
    have vLow : q.loV< -(11/50)*q.s := by
      apply lt_of_not_ge
      intro bad
      have first := mul_nonneg sn (show 0≤q.loU+(3/5)*q.c by linarith only [fU])
      have last := mul_nonneg cp.le (show 0≤q.loV+(11/50)*q.s by linarith only [bad])
      have extra := mul_pos (sub_pos.mpr side)
        (show 0<q.c+q.s by linarith only [sumLow])
      nlinarith only [first,last,extra,wall,arc]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]
  · have vLow : q.loV< -(11/50)*q.s := by linarith only [fV,side,su]
    have hHighU : -(1/5)*q.s<q.loU+q.side := by linarith only [origin.2.1,sn]
    have hHighV : -(1/5)*q.c<q.loV+q.side := by linarith only [origin.2.2.2,cp]
    have hLowV : q.loV< -(1/5)*q.c := by
      have short := (short_projections q (1/5) (3/5) (by norm_num)).2.1
      linarith only [fV,short,side]
    have hFace : -(1/5)*q.s≤q.loU := by
      apply le_of_not_gt
      intro low
      apply missingBelow
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [low,hHighU,hLowV,hHighV]
    have short := (short_projections q (11/50) (1/5) (by norm_num)).2.1
    have uHigh : (11/50)*q.c<q.loU+q.side := by linarith only [hFace,short,side]
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [uLow,uHigh,vLow,vHigh]

theorem point (q : OpenSquare) (side : 1<q.side)
    (wall : ∀ x y,q.Inside x y → y≤1)
    (origin : q.Inside 0 0) (missingLeft : ¬q.Inside (-(3/5)) 0)
    (missingBelow : ¬q.Inside 0 (-(1/5))) : q.Inside (11/50) 0 := by
  obtain ⟨r,cp,sn,shape,same,_⟩ := ClosedFrames.positive_frame q
  have wall' : ∀ x y,r.Inside x y → y≤1 :=
    fun x y own => wall x y ((same _ _).mp own)
  exact (same _ _).mp (positive r (by simpa only [shape] using side) cp sn
    (C981CompletionCornerAdvance.upper_wall r wall') ((same _ _).mpr origin)
    (fun h => missingLeft ((same _ _).mp h)) (fun h => missingBelow ((same _ _).mp h)))

#print axioms point
end N12Compact.Completion.OtherCases.ShortCornerAdvance

