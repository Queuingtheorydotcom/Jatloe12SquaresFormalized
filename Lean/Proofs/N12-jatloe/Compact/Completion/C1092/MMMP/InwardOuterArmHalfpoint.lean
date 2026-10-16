import Compact.Completion.C1092.MMMP.BottomOrigin
import Compact.Completion.CommonCases.CanonicalScalars

/-! INWARD-OUTER-ARM-HALFPOINT, Theorem 1 and Corollary 2. The local
theorem uses the entire excluded short bar and covers both canonical
signs, including axial and diagonal frames. Its application keeps the
actual southeast, right, bottom, and corner owners distinct.
Source translation only; compiler acceptance has not been tested. -/
namespace N12Compact.C1092MMMPInwardOuterArmHalfpoint
open S12 S12Pilot C1092WallCycle C1092WallSymmetry
open C1092MMMPEntrance C1092MMMPOrigins C1092MMMPPointCore
open C1092WallProfileScalars
set_option Elab.async false

private theorem negative_impossible (C : OpenSquare) (s : ℝ)
    (signed : C.s= -s) (side : 1<C.side)
    (cp : 0<C.c) (sn : 0≤s) (order : s≤C.c)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (A : C.Inside (2/5) 1)
    (F : ¬C.Inside (13/50) 1) (E : ¬C.Inside 1 (2/5)) : False := by
  have m := M
  have i := I
  have j := J
  have a := A
  simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_zero,zero_mul,
    mul_one,zero_add,add_zero] at m i j a
  have low : (13/50)*C.c-s≤C.loU := by
    apply le_of_not_gt
    intro first
    apply F
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [first,a.2.1,a.2.2.2,i.2.2.1,cp,sn]
  have high : C.loU+C.side≤C.c-(2/5)*s := by
    apply le_of_not_gt
    intro last
    apply E
    simp only [OpenSquare.Inside,InBands,signed,neg_neg,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [j.1,m.2.2.1,a.2.2.2,last,cp,sn,order]
  have short := (short_projections C (37/50) (-3/5) (by norm_num)).2.1
  rw [signed] at short
  linarith only [low,high,short,side]

private theorem positive_point (C : OpenSquare) (side : 1<C.side)
    (cp : 0<C.c) (sn : 0≤C.s) (order : C.s≤C.c)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (A : C.Inside (2/5) 1)
    (O : ¬C.Inside 0 0) (F : ¬C.Inside (13/50) 1)
    (bar : ∀ y : ℝ,13/50≤y → y≤2/5 → ¬C.Inside 1 y) :
    C.Inside (1/2) 1 := by
  have m := M
  have i := I
  have j := J
  have a := A
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,mul_one,
    zero_add,add_zero] at m i j a
  have lower : 0≤C.loU := by
    apply le_of_not_gt
    intro low
    apply O
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero]
    refine ⟨low,?_,?_,?_⟩ <;>
      linarith only [m.2.1,j.2.2.1,i.2.2.2,cp,sn]
  have sp : 0<C.s := by linarith only [lower,i.1]
  have cap : C.loV+C.side≤C.c-(13/50)*C.s := by
    apply le_of_not_gt
    intro high
    apply F
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,by linarith only [high]⟩ <;>
      linarith only [i.1,a.2.1,a.2.2.1,cp,sn]
  by_contra missing
  have upper : C.loU+C.side≤C.c/2+C.s := by
    apply le_of_not_gt
    intro high
    apply missing
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [a.1,a.2.2.2,j.2.2.1,high,cp,sn,order]
  have span : 1<C.c/2+C.s := by linarith only [lower,upper,side]
  have bounds := CommonCases.CanonicalScalars.bounds C.c C.s cp sn order C.unit_normal
  have data := quarter_data C.c C.s cp.le sn C.unit_normal
  let z := half C.c C.s
  have zp : 0<z := div_pos sp (by linarith only [cp])
  have zu : z<1 := (div_lt_one (by linarith only [cp])).mpr
    (by linarith only [order])
  have cosine : (1+z^2)*C.c=1-z^2 := data.2.2.2.1
  have sine : (1+z^2)*C.s=2*z := data.2.2.2.2
  have relation : z*(1+C.c)=C.s := data.2.2.1
  have unitAngle : C.s*z=1-C.c :=
    (C1092MMMPPositiveInwardHalfangle.half_identities C.c C.s cp C.unit_normal).2
  have large : 1/3<z := by
    apply lt_of_not_ge
    intro small
    have weighted := mul_pos (show 0<1+z^2 by positivity) (sub_pos.mpr span)
    have endpoint := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr zu.le)
      (show 3*z-1≤0 by linarith only [small])
    nlinarith only [weighted,cosine,sine,endpoint]
  have sLarge : 3/5<C.s := by
    have weighted := mul_pos (show 0<z-1/3 by linarith only [large])
      (show 0<1+C.c by linarith only [cp])
    have ratio : 1+C.c<3*C.s := by nlinarith only [weighted,relation]
    apply lt_of_not_ge
    intro small
    have cSmall : C.c<4/5 := by linarith only [ratio,small]
    have first := mul_pos (sub_pos.mpr cSmall)
      (show 0<4/5+C.c by linarith only [cp])
    have last := mul_nonneg (show 0≤3/5-C.s by linarith only [small])
      (show 0≤3/5+C.s by linarith only [sn])
    nlinarith only [first,last,C.unit_normal]
  have margin : 37/50<C.s+(13/50)*C.c := by
    linarith only [sLarge,bounds.1]
  have u : C.c+C.s*z=1 := by linarith only [unitAngle]
  have v : -C.s+C.c*z= -z := by nlinarith only [relation]
  have identity : C.c-(13/50)*C.s+z-1=
      z*(37/50-C.s-(13/50)*C.c) := by
    nlinarith only [relation,unitAngle]
  have negative := mul_neg_of_pos_of_neg zp
    (show 37/50-C.s-(13/50)*C.c<0 by linarith only [margin])
  have zInside : C.Inside 1 z := by
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · nlinarith only [i.1,u,bounds.2.1,order]
    · nlinarith only [u,lower,side]
    · nlinarith only [v,identity,negative,cap,side]
    · nlinarith only [v,i.2.2.2,zp,cp]
  by_cases within : z≤2/5
  · exact bar z (by linarith only [large]) within zInside
  · have high : 2/5<z := lt_of_not_ge within
    have weighted := mul_pos sp (sub_pos.mpr high)
    have short := (short_projections C (3/5) (37/50) (by norm_num)).2.1
    apply bar (2/5) (by norm_num) le_rfl
    simp only [OpenSquare.Inside,InBands,mul_one]
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [j.1,cp,sn]
    · nlinarith only [weighted,u,lower,side]
    · linarith only [short,cap,side]
    · linarith only [i.2.2.2,sLarge,bounds.2.1]

/-- The literal local point-and-bar theorem, without a side upper bound. -/
theorem point (C : OpenSquare) (side : 1<C.side)
    (M : C.Inside (7/20) (7/20)) (I : C.Inside 0 (13/50))
    (J : C.Inside (13/50) 0) (A : C.Inside (2/5) 1)
    (O : ¬C.Inside 0 0) (F : ¬C.Inside (13/50) 1)
    (bar : ∀ y : ℝ,13/50≤y → y≤2/5 → ¬C.Inside 1 y) :
    C.Inside (1/2) 1 := by
  obtain ⟨q,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame C
  have side' : 1<q.side := by simpa only [shape] using side
  have m := (same _ _).mpr M
  have i := (same _ _).mpr I
  have j := (same _ _).mpr J
  have a := (same _ _).mpr A
  have f : ¬q.Inside (13/50) 1 := fun own => F ((same _ _).mp own)
  have b : ∀ y : ℝ,13/50≤y → y≤2/5 → ¬q.Inside 1 y :=
    fun y low high own => bar y low high ((same _ _).mp own)
  apply (same _ _).mp
  by_cases sign : 0≤q.s
  · exact positive_point q side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m i j a
      (fun own => O ((same _ _).mp own)) f b
  · exact False.elim (negative_impossible q (-q.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
      m i j a f (b (2/5) (by norm_num) le_rfl))

/-- The original southeast halfpoint, with its full actual-owner ledger. -/
theorem halfpoint_of_outer (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (outer : (owners p 5).Inside 3 (8/5)) :
    (owners p 5).Inside 3 (3/2) := by
  have inward := C1092MMMPSoutheastSign.inward_pair p hf hb near
  have bottom := C1092MMMPBottomPair.pair p hf hb
  have mark : (owners p 5).Inside (47/20) (33/20) := by
    simpa [marker] using marker_point p hf 5 9 (by decide +kernel)
  let C := (pullSwap (pullY (owners p 5))).translated 2 2
  have actual (x y : ℝ) : C.Inside x y ↔ (owners p 5).Inside (2+y) (2-x) := by
    simp only [C,inside_translated_iff,inside_pullSwap,inside_pullY]
    rw [show 4-(2+x)=2-x by ring]
  have h := point C (side_gt p 5)
    (by apply (actual _ _).mpr; norm_num; exact mark)
    (by apply (actual _ _).mpr; norm_num; exact inward.2)
    (by apply (actual _ _).mpr; norm_num; exact inward.1)
    (by apply (actual _ _).mpr; norm_num; exact outer)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 5 7 (by decide) _ _
        ⟨own',northwest_center p hf hb⟩)
    (by
      intro own
      have own' := (actual _ _).mp own
      norm_num at own'
      exact owners_disjoint p hf 5 10 (by decide) _ _ ⟨own',near⟩)
    (by
      intro y low high own
      have own' := (actual _ _).mp own
      norm_num at own'
      let t := (y-13/50)/(7/50)
      have tn : 0≤t := div_nonneg (by linarith only [low]) (by norm_num)
      have tu : t≤1 := (div_le_one (by norm_num)).mpr (by linarith only [high])
      have segment := inside_segment (owners p 9) (113/50) 1 (12/5) 1 t
        bottom.2 bottom.1 tn tu
      have foreign : (owners p 9).Inside (2+y) 1 := by
        convert segment using 1
        · dsimp only [t]; ring
        · ring
      exact owners_disjoint p hf 5 9 (by decide) _ _ ⟨own',foreign⟩)
  have original := (actual _ _).mp h
  norm_num at original
  exact original

/-- Corollary 2 uses the genuine reflected corner-to-wall transfer. -/
theorem bottom_origin_of_outer (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50))
    (outer : (owners p 5).Inside 3 (8/5)) :
    (owners p 9).Inside 2 1 := by
  classical
  by_contra missing
  exact owners_disjoint p hf 5 1 (by decide) _ _
    ⟨halfpoint_of_outer p hf hb near outer,
      C1092MMMPBottomOriginEntrance.corner_halfpoint p hf hb missing⟩

/-- The two genuine outer-point alternatives remove the extra omission
premise: actual right F8 alone now supplies the original bottom origin. -/
theorem bottom_origin_of_near (p : NormalizedPacking)
    (hf : codedMarkerFamily p=family) (hb : WallContext p mmmp)
    (near : (owners p 10).Inside 3 (87/50)) :
    (owners p 9).Inside 2 1 := by
  by_cases outer : (owners p 5).Inside 3 (8/5)
  · exact bottom_origin_of_outer p hf hb near outer
  · exact C1092MMMPBottomOrigin.point_of_near p hf hb near outer

#print axioms point
#print axioms halfpoint_of_outer
#print axioms bottom_origin_of_outer
#print axioms bottom_origin_of_near
end N12Compact.C1092MMMPInwardOuterArmHalfpoint
