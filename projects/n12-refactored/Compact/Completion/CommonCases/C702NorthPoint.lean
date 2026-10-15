import Compact.Completion.CommonCases.C702NorthScalars
import Compact.Completion.CommonCases.LowerSegmentSupport
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! C702-N-STRICT-POINT, with both whole foreign segments retained. -/
namespace N12Compact.CommonCases.C702NorthPoint
open S12 S12Pilot
set_option Elab.async false

private def TopAvoid (q : OpenSquare) : Prop :=
  ∀ x : ℝ, 1/5≤x → x≤37/50 → ¬q.Inside x 1
private def LeftAvoid (q : OpenSquare) : Prop :=
  ∀ w : ℝ, 0≤w → w≤1 →
    ¬q.Inside ((1-w)*(-6/25)) ((1-w)*(-13/100)+w*(-13/50))

private theorem top_support (q : OpenSquare)
    (u0Low : q.loU < q.c*(1/5)+q.s)
    (u0High : q.c*(1/5)+q.s < q.loU+q.side)
    (v0Face : q.loV+q.side ≤ q.c-q.s*(1/5))
    (u1Face : q.loU+q.side ≤ q.c*(37/50)+q.s)
    (v1Low : q.loV < q.c-q.s*(37/50))
    (v1High : q.c-q.s*(37/50) < q.loV+q.side) (avoid : TopAvoid q) :
    q.s*(q.loU+q.side)+q.c*(q.loV+q.side) ≤ 1 := by
  let u0 := -(q.c*(37/50)+q.s)
  let v0 := -(q.c-q.s*(37/50))
  let u1 := -(q.c*(1/5)+q.s)
  let v1 := -(q.c-q.s*(1/5))
  have cut := LowerSegmentSupport.support (-(q.loU+q.side)) (-q.loU)
    (-(q.loV+q.side)) (-q.loV) u0 v0 u1 v1
    (by dsimp [u0]; linarith only [u1Face])
    (by dsimp [u1]; linarith only [u0High])
    (by dsimp [u1]; linarith only [u0Low])
    (by dsimp [v0]; linarith only [v1High])
    (by dsimp [v0]; linarith only [v1Low])
    (by dsimp [v1]; linarith only [v0Face])
    (by
      intro w wn wu own
      apply avoid ((1-w)*(37/50)+w*(1/5))
        (by linarith only [wu]) (by linarith only [wn])
      change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
      dsimp [u0,v0,u1,v1] at own
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  dsimp [u0,v0,u1,v1] at cut
  nlinarith only [cut,q.unit_normal]

private theorem left_support (q : OpenSquare)
    (sFace : q.c*(-6/25)+q.s*(-13/100) ≤ q.loU)
    (sLow : q.loV < -q.s*(-6/25)+q.c*(-13/100))
    (sHigh : -q.s*(-6/25)+q.c*(-13/100) < q.loV+q.side)
    (lLow : q.loU < q.s*(-13/50)) (lHigh : q.s*(-13/50) < q.loU+q.side)
    (lFace : q.c*(-13/50) ≤ q.loV) (avoid : LeftAvoid q) :
    -(39/625) ≤ ((13/100)*q.c+(6/25)*q.s)*q.loU+
      ((6/25)*q.c-(13/100)*q.s)*q.loV := by
  let u0 := q.c*(-6/25)+q.s*(-13/100)
  let v0 := -q.s*(-6/25)+q.c*(-13/100)
  let u1 := q.s*(-13/50)
  let v1 := q.c*(-13/50)
  have cut := LowerSegmentSupport.support q.loU (q.loU+q.side) q.loV (q.loV+q.side)
    u0 v0 u1 v1 sFace lLow lHigh sLow sHigh lFace
    (by
      intro w wn wu own
      apply avoid w wn wu
      change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
      dsimp [u0,v0,u1,v1] at own
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  dsimp [u0,v0,u1,v1] at cut
  nlinarith only [cut,q.unit_normal]

private theorem negative (q : OpenSquare) (t : ℝ) (signed : q.s=-t)
    (side : 1 < q.side) (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c)
    (p : q.Inside (-43/500) 0) (m : q.Inside (13/20) (7/20))
    (h : q.Inside 0 (13/50)) (missingD : ¬q.Inside (1/2) 0)
    (missingK : ¬q.Inside 0 1) (avoid : LeftAvoid q) : q.Inside (3/10) (-7/100) := by
  classical
  have missingL := avoid 1 (by norm_num) (by norm_num)
  norm_num at missingL
  simp only [OpenSquare.Inside,InBands,signed,mul_zero,zero_add,add_zero,mul_one,neg_neg]
    at p m h missingD missingK missingL ⊢
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have slope : 3*q.c < 7*t := by
    by_contra bad
    have shallow : 7*t ≤ 3*q.c := by exact le_of_not_gt bad
    apply missingD
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [p.1,p.2.2.1,m.2.1,m.2.2.2,shallow,cp,tn,order]
  have lowU : q.loU < q.c*(3/10)+(-t)*(-7/100) := by
    linarith only [p.1,cp,tn]
  have lowV : q.loV < t*(3/10)+q.c*(-7/100) := by
    linarith only [p.2.2.1,slope,cp]
  have highV : t*(3/10)+q.c*(-7/100) < q.loV+q.side := by
    linarith only [m.2.2.2,cp,tn]
  have highU : q.c*(3/10)+(-t)*(-7/100) < q.loU+q.side := by
    by_cases shallow : 6*t ≤ 5*q.c
    · linarith only [m.2.1,shallow]
    · by_contra bad
      have face : q.loU+q.side ≤ q.c*(3/10)+(-t)*(-7/100) := by exact le_of_not_gt bad
      have short := OutwardScalars.increasing_projection q.c t (3/10) (107/100)
        cp tn order unit (by norm_num) (by norm_num) (by norm_num)
      have kLowU : q.loU < -t := by linarith only [face,side,short]
      have kHighU : -t < q.loU+q.side := by linarith only [m.2.1,cp,tn]
      have kLowV : q.loV < q.c := by linarith only [h.2.2.1,cp]
      have kFace : q.loV+q.side ≤ q.c :=
        le_of_not_gt (fun own => missingK ⟨kLowU,kHighU,kLowV,own⟩)
      have lLowU : q.loU < (-t)*(-13/50) := by linarith only [p.1,cp,tn]
      have lHighU : (-t)*(-13/50) < q.loU+q.side := by linarith only [m.2.1,cp,order]
      have lHighV : q.c*(-13/50) < q.loV+q.side := by linarith only [h.2.2.2,cp]
      have lFace : q.c*(-13/50) ≤ q.loV := by
        apply le_of_not_gt
        intro own
        apply missingL
        refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lLowU,lHighU,own,lHighV]
      have shortC := C702NorthScalars.negative_gap q.c t cp tn unit (lt_of_not_ge shallow)
      linarith only [kFace,lFace,side,shortC]
  exact ⟨lowU,highU,lowV,highV⟩

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (p : q.Inside (-43/500) 0) (m : q.Inside (13/20) (7/20))
    (h : q.Inside 0 (13/50)) (missingD : ¬q.Inside (1/2) 0)
    (missingK : ¬q.Inside 0 1) (top : TopAvoid q) (left : LeftAvoid q) :
    q.Inside (3/10) (-7/100) := by
  classical
  simp only [OpenSquare.Inside,InBands,mul_zero,zero_add,add_zero,mul_one] at missingD missingK
  have cu := (CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal).2.1
  have dLowU : q.loU < q.c*(1/2) := by linarith only [p.1,cp]
  have dHighU : q.c*(1/2) < q.loU+q.side := by linarith only [m.2.1,cp,sn]
  have dHighV : -q.s*(1/2) < q.loV+q.side := by linarith only [m.2.2.2,cp,order]
  have dFace : -q.s*(1/2) ≤ q.loV :=
    le_of_not_gt (fun own => missingD ⟨dLowU,dHighU,own,dHighV⟩)
  have sp : 0 < q.s := by
    by_contra bad
    have zero : q.s=0 := le_antisymm (by exact le_of_not_gt bad) sn
    have lower := p.2.2.1
    rw [zero] at lower dFace
    linarith only [lower,dFace]
  have kLowU : q.loU < q.s := by linarith only [p.1,cp,sn]
  have kHighU : q.s < q.loU+q.side := by linarith only [m.2.1,order]
  have kLowV : q.loV < q.c := by linarith only [h.2.2.1,cp]
  have kFace : q.loV+q.side ≤ q.c :=
    le_of_not_gt (fun own => missingK ⟨kLowU,kHighU,kLowV,own⟩)
  have t0LowU : q.loU < q.c*(1/5)+q.s := by linarith only [p.1,cp,sn]
  have t0LowV : q.loV < q.c-q.s*(1/5) := by linarith only [p.2.2.1,cp,order]
  have t1LowU : q.loU < q.c*(37/50)+q.s := by linarith only [p.1,cp,sn]
  have t1LowV : q.loV < q.c-q.s*(37/50) := by linarith only [p.2.2.1,cp,order]
  have t1HighV : q.c-q.s*(37/50) < q.loV+q.side := by linarith only [dFace,side,cu,sn]
  have t1Face : q.loU+q.side ≤ q.c*(37/50)+q.s := by
    apply le_of_not_gt
    intro own
    apply top (37/50) (by norm_num) le_rfl
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [t1LowU,own,t1LowV,t1HighV]
  have steep : 9*q.c < 13*q.s := by
    by_contra bad
    have shallow : 13*q.s ≤ 9*q.c := by exact le_of_not_gt bad
    have t0HighU : q.c*(1/5)+q.s < q.loU+q.side := by linarith only [m.2.1,shallow]
    have t0Face : q.loV+q.side ≤ q.c-q.s*(1/5) := by
      apply le_of_not_gt
      intro own
      apply top (1/5) le_rfl (by norm_num)
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [t0LowU,t0HighU,t0LowV,own]
    have support := top_support q t0LowU t0HighU t0Face t1Face t1LowV t1HighV top
    have margin := C702NorthScalars.shallow_margin q.c q.s cp sp order q.unit_normal shallow
    have uWeighted := mul_pos sp (show 0 < q.loU+q.side-(q.c*(13/20)+q.s*(7/20))
      by linarith only [m.2.1])
    have vWeighted := mul_pos cp (show 0 < q.loV+q.side-(1-q.s*(1/2))
      by linarith only [dFace,side])
    nlinarith only [support,margin,uWeighted,vWeighted]
  have bounds := C702NorthScalars.steep_bounds q.c q.s cp sn q.unit_normal steep
  have shortT0 := CanonicalProjection.after q.c q.s (91/109) (60/109) 1 (3/10)
    q.unit_normal (by norm_num) (by linarith only [steep,cp]) (by norm_num) (by norm_num)
  norm_num at shortT0
  have t0HighV : q.c-q.s*(1/5) < q.loV+q.side := by linarith only [dFace,side,shortT0]
  have t0Face : q.loU+q.side ≤ q.c*(1/5)+q.s := by
    apply le_of_not_gt
    intro own
    apply top (1/5) le_rfl (by norm_num)
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [t0LowU,own,t0LowV,t0HighV]
  have missingS := left 0 (by norm_num) (by norm_num)
  have missingL := left 1 (by norm_num) (by norm_num)
  norm_num at missingS missingL
  have sHighU : q.c*(-6/25)+q.s*(-13/100) < q.loU+q.side := by linarith only [p.2.1,cp,sn]
  have sHighV : -q.s*(-6/25)+q.c*(-13/100) < q.loV+q.side := by
    linarith only [h.2.2.2,cp,order]
  have sLowV : q.loV < -q.s*(-6/25)+q.c*(-13/100) := by
    linarith only [kFace,side,bounds.1,sn]
  have sFace : q.c*(-6/25)+q.s*(-13/100) ≤ q.loU := by
    apply le_of_not_gt
    intro own
    apply missingS
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [own,sHighU,sLowV,sHighV]
  have lHighU : q.s*(-13/50) < q.loU+q.side := by linarith only [m.2.1,cp,sn]
  have lHighV : q.c*(-13/50) < q.loV+q.side := by linarith only [h.2.2.2,cp]
  have lFace : q.s*(-13/50) ≤ q.loU := by
    apply le_of_not_gt
    intro lLowU
    have lLowFace : q.c*(-13/50) ≤ q.loV := by
      apply le_of_not_gt
      intro own
      apply missingL
      refine ⟨?_,?_,?_,?_⟩ <;> linarith only [lLowU,lHighU,own,lHighV]
    have cLow : 50/63 < q.c := by linarith only [kFace,lLowFace,side]
    have support := left_support q sFace sLowV sHighV lLowU lHighU lLowFace left
    let α := (13/100)*q.c+(6/25)*q.s
    let β := (6/25)*q.c-(13/100)*q.s
    have ap : 0 < α := by dsimp [α]; linarith only [cp,sn]
    have bp : 0 < β := by dsimp [β]; linarith only [cp,order]
    have uWeighted := mul_nonneg ap.le
      (show 0 ≤ q.c*(1/5)+q.s-(q.loU+q.side) by linarith only [t0Face])
    have vWeighted := mul_nonneg bp.le
      (show 0 ≤ q.c-(q.loV+q.side) by linarith only [kFace])
    have coefficient : 881/2500 < (37/100)*q.c+(11/100)*q.s := by
      linarith only [cLow,bounds.2]
    have width := mul_pos (sub_pos.mpr side)
      (show 0 < (37/100)*q.c+(11/100)*q.s by linarith only [coefficient])
    dsimp [α,β] at uWeighted vWeighted
    nlinarith only [support,uWeighted,vWeighted,q.unit_normal,sq_nonneg (q.c-q.s),
      sq_nonneg q.s,coefficient,width]
  have span : 1 < (1/5)*q.c+(63/50)*q.s := by linarith only [lFace,t0Face,side]
  have cutoff : (1900/2861)*q.c < (2139/2861)*q.s := by
    apply lt_of_not_ge
    intro reverse
    have short := CanonicalProjection.before q.c q.s (2139/2861) (1900/2861) (1/5) (63/50)
      q.unit_normal (by norm_num) reverse (by norm_num) (by norm_num)
    norm_num at short
    linarith only [span,short]
  have short := CanonicalProjection.after q.c q.s (2139/2861) (1900/2861) (107/100) (3/10)
    q.unit_normal (by norm_num) cutoff.le (by norm_num) (by norm_num)
  norm_num at short
  refine ⟨?_,?_,?_,?_⟩
  · linarith only [p.1,cp,order]
  · linarith only [m.2.1,cp,sn]
  · linarith only [kFace,side,short]
  · linarith only [p.2.2.2,cp,sn]

theorem point (q : OpenSquare) (side : 1 < q.side)
    (p : q.Inside (-43/500) 0) (m : q.Inside (13/20) (7/20))
    (h : q.Inside 0 (13/50)) (missingD : ¬q.Inside (1/2) 0)
    (missingK : ¬q.Inside 0 1)
    (top : ∀ x : ℝ, 1/5≤x → x≤37/50 → ¬q.Inside x 1)
    (left : ∀ w : ℝ, 0≤w → w≤1 →
      ¬q.Inside ((1-w)*(-6/25)) ((1-w)*(-13/100)+w*(-13/50))) :
    q.Inside (3/10) (-7/100) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have pp := (same _ _).mpr p
  have mm := (same _ _).mpr m
  have hh := (same _ _).mpr h
  have d : ¬r.Inside (1/2) 0 := fun own => missingD ((same _ _).mp own)
  have k : ¬r.Inside 0 1 := fun own => missingK ((same _ _).mp own)
  have tt : TopAvoid r := fun x lo hi own => top x lo hi ((same _ _).mp own)
  have ll : LeftAvoid r := fun w lo hi own => left w lo hi ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) pp mm hh d k tt ll)
  · exact (same _ _).mp (negative r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) pp mm hh d k ll)

theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (p : q.Inside (457/500) 2) (m : q.Inside (33/20) (47/20))
    (h : q.Inside 1 (113/50)) (missingD : ¬q.Inside (3/2) 2)
    (missingK : ¬q.Inside 1 3)
    (top : ∀ x : ℝ, 6/5≤x → x≤87/50 → ¬q.Inside x 3)
    (left : ∀ w : ℝ, 0≤w → w≤1 →
      ¬q.Inside ((1-w)*(19/25)+w) ((1-w)*(187/100)+w*(87/50))) :
    q.Inside (13/10) (193/100) := by
  have answer := point (q.translated 1 2) side
    (by norm_num [inside_translated_iff]; exact p)
    (by norm_num [inside_translated_iff]; exact m)
    (by norm_num [inside_translated_iff]; exact h)
    (by norm_num [inside_translated_iff]; exact missingD)
    (by norm_num [inside_translated_iff]; exact missingK)
    (by
      intro x lo hi own
      norm_num [inside_translated_iff] at own
      exact top (1+x) (by linarith only [lo]) (by linarith only [hi]) own)
    (by
      intro w wn wu own
      apply left w wn wu
      norm_num [inside_translated_iff] at own
      convert own using 1 <;> ring)
  norm_num [inside_translated_iff] at answer
  exact answer

#print axioms point_original
end N12Compact.CommonCases.C702NorthPoint
