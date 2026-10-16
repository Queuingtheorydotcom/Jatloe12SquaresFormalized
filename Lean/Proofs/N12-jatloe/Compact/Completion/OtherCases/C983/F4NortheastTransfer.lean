import Compact.Completion.OtherCases.C983.F4CornerEntrance
import Compact.Completion.OtherCases.C983.PositiveMixedTransfer
import Compact.Completion.OtherCases.C1090.ResidualCentralPoints

/-! The two genuine northeast alternatives supply an actual sharp point
and the right-wall origin. The mixed negative transfer is Theorem 1 of
C974-C976-FINAL-ANGLE-REDUCTIONS, proved here by two unit-circle factors.
No northeast sign, omitted point, or separate northwest square is assumed. -/
namespace N12Compact.Completion.OtherCases.C983
open S12 S12Pilot
set_option Elab.async false
noncomputable section

theorem negative_mixed_transfer (N : OpenSquare) (side : 1<N.side)
    (cp : 0<N.c) (sn : N.s≤0) (order : -N.s≤N.c)
    (marker : N.Inside (7/20) (7/20))
    (near : N.Inside 0 (13/50)) (far : N.Inside (13/50) 1)
    (missingP : ¬N.Inside 0 1) (missingD : ¬N.Inside (13/50) 0)
    (missingX : ¬N.Inside (1/2) 0) : N.Inside (1/2) 1 := by
  let s := -N.s
  have sp : 0≤s := by dsimp only [s]; linarith only [sn]
  have sc : s≤N.c := order
  have signed : N.s= -s := by dsimp only [s]; ring
  have unit : N.c^2+s^2=1 := by simpa only [s,neg_sq] using N.unit_normal
  have cu : N.c≤1 := by nlinarith only [unit,sq_nonneg s,cp]
  have sum : N.c+s≤3/2 := by
    nlinarith only [unit,sq_nonneg (N.c-s),cp,sp]
  have m := marker
  have f := near
  have g := far
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,mul_one,
    zero_add] at m f g
  have lowerU : -s≤N.loU := by
    apply le_of_not_gt
    intro low
    apply missingP
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,mul_one,
      zero_add]
    refine ⟨low,?_,?_,?_⟩ <;> linarith only [g.2.1,g.2.2.2,m.2.2.1,cp,sp,sc]
  have lowerV : (13/50)*s≤N.loV := by
    apply le_of_not_gt
    intro low
    apply missingD
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [f.1,g.2.2.2,lowerU,side,sum,cp,sp,sc,low]
  by_contra missing
  have upperV : N.loV+N.side≤s/2+N.c := by
    apply le_of_not_gt
    intro high
    apply missing
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [g.1,g.2.2.1,lowerU,side,cu,high,cp,sp]
  have upperU : N.loU+N.side≤N.c/2 := by
    apply le_of_not_gt
    intro high
    apply missingX
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,add_zero]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [m.1,m.2.2.2,upperV,side,cu,high,cp,sp,sc]
  have steep : (3/4)*N.c<s := by
    apply lt_of_not_ge
    intro small
    have product := mul_nonneg cp.le (show 0≤(3/4)*N.c-s by linarith only [small])
    have width : 1<N.c/2+s := by linarith only [upperU,lowerU,side]
    have square := mul_pos (sub_pos.mpr width)
      (show 0<N.c/2+s+1 by positivity)
    nlinarith only [unit,product,square]
  have width : 1<N.c+(6/25)*s := by linarith only [lowerV,upperV,side]
  have square := mul_pos (sub_pos.mpr width)
    (show 0<N.c+(6/25)*s+1 by positivity)
  have product := mul_nonneg sp
    (show 0≤(589/625)*s-(12/25)*N.c by linarith only [steep,cp])
  nlinarith only [unit,product,square]

theorem f4_northeast_extension (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    (owners p 6).Inside (5/2) 3 := by
  by_cases mixed : 5∈actual p 6
  · have marker : (owners p 6).Inside (47/20) (47/20) := by
      convert seed_inside p hf 6 (47/20,47/20) (by decide +kernel) using 1 <;> norm_num
    have near : (owners p 6).Inside 2 (113/50) := by
      simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 6 5 (by decide +kernel) mixed
    have far : (owners p 6).Inside (113/50) 3 := by
      simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 6 17 (by decide +kernel)
        (f4_northeast_g7 p hf f4)
    have elbow : (owners p 5).Inside (113/50) 2 := by
      simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 5 16 (by decide +kernel)
        (f4_southeast_g6 p hf f4)
    obtain ⟨N,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame
      ((owners p 6).translated 2 2)
    have transport (x y : ℝ) : N.Inside x y↔(owners p 6).Inside (2+x) (2+y) := by
      rw [inside,inside_translated_iff]
    have point : N.Inside (1/2) 1 := by
      by_cases sign : 0≤N.s
      · apply positive_mixed_transfer N (by simpa only [shape,OpenSquare.translated] using owners_side p 6)
          cp sign ((abs_le.mp range).2)
        · apply (transport _ _).mpr; norm_num; exact near
        · apply (transport _ _).mpr; norm_num; exact far
        · intro own
          have original := (transport _ _).mp own
          norm_num at original
          exact owners_apart p hf 6 7 (by decide +kernel) _ _
            ⟨original,f4_merged_center p hf f4⟩
        · intro own
          have original := (transport _ _).mp own
          norm_num at original
          exact owners_apart p hf 6 11 (by decide +kernel) _ _
            ⟨original,f4_top_origin p hf f4⟩
        · intro own
          have original := (transport _ _).mp own
          norm_num at original
          exact owners_apart p hf 6 5 (by decide +kernel) _ _ ⟨original,elbow⟩
      · apply negative_mixed_transfer N (by simpa only [shape,OpenSquare.translated] using owners_side p 6)
          cp (le_of_not_ge sign) (by linarith only [(abs_le.mp range).1])
        · apply (transport _ _).mpr; norm_num; exact marker
        · apply (transport _ _).mpr; norm_num; exact near
        · apply (transport _ _).mpr; norm_num; exact far
        · intro own
          have original := (transport _ _).mp own
          norm_num at original
          exact owners_apart p hf 6 11 (by decide +kernel) _ _
            ⟨original,f4_top_origin p hf f4⟩
        · intro own
          have original := (transport _ _).mp own
          norm_num at original
          exact owners_apart p hf 6 5 (by decide +kernel) _ _ ⟨original,elbow⟩
        · intro own
          have original := (transport _ _).mp own
          norm_num at original
          exact owners_apart p hf 6 5 (by decide +kernel) _ _
            ⟨original,f4_southeast_crosspoint p hf f4⟩
    have original := (transport _ _).mp point
    norm_num at original
    exact original
  · exact (f4_top_only_points p hf f4 mixed).2.1

theorem f4_right_origin (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    (owners p 10).Inside 3 2 :=
  right_origin_of_upper_extension p hf (f4_right p hf f4).2
    (f4_northeast_extension p hf f4)

theorem f4_northeast_sharp (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (f4 : 4∈actual p 7) :
    (owners p 6).Inside (101/40) (17/8) ∨
      (owners p 6).Inside (121/50) (54/25) := by
  by_cases mixed : 5∈actual p 6
  · right
    have marker : (owners p 6).Inside (47/20) (47/20) := by
      convert seed_inside p hf 6 (47/20,47/20) (by decide +kernel) using 1 <;> norm_num
    have near : (owners p 6).Inside 2 (113/50) := by
      simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 6 5 (by decide +kernel) mixed
    have far : (owners p 6).Inside (113/50) 3 := by
      simpa [auxPoints,fPoints,gPoints] using auxiliary_inside p 6 17 (by decide +kernel)
        (f4_northeast_g7 p hf f4)
    have northwest : (owners p 7).Inside (33/20) (47/20) := by
      convert seed_inside p hf 7 (33/20,47/20) (by decide +kernel) using 1 <;> norm_num
    have corner : (owners p 3).Inside 3 3 := by
      convert seed_inside p hf 3 (3,3) (by decide +kernel) using 1 <;> norm_num
    have right : (owners p 10).Inside 3 (113/50) :=
      f4_right_bar p hf f4 _ le_rfl (by norm_num)
    have point := C1090.ResidualCentralPoints.mixed_point ((owners p 6).translated 2 2)
      (owners_side p 6)
      (by norm_num [inside_translated_iff]; exact marker)
      (by norm_num [inside_translated_iff]; exact near)
      (by norm_num [inside_translated_iff]; exact far)
      (by norm_num [inside_translated_iff]; exact fun own =>
        owners_apart p hf 6 7 (by decide +kernel) _ _ ⟨own,northwest⟩)
      (by norm_num [inside_translated_iff]; exact fun own =>
        owners_apart p hf 6 11 (by decide +kernel) _ _ ⟨own,f4_top_origin p hf f4⟩)
      (by norm_num [inside_translated_iff]; exact fun own =>
        owners_apart p hf 6 3 (by decide +kernel) _ _ ⟨own,corner⟩)
      (by norm_num [inside_translated_iff]; exact fun own =>
        owners_apart p hf 6 10 (by decide +kernel) _ _ ⟨own,right⟩)
    norm_num [inside_translated_iff] at point
    exact point
  · exact Or.inl (f4_top_only_points p hf f4 mixed).1

end
#print axioms negative_mixed_transfer
#print axioms f4_right_origin
#print axioms f4_northeast_sharp
end N12Compact.Completion.OtherCases.C983
