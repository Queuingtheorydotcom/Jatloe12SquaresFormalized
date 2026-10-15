import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Completion.CommonCases.LowerSegmentSupport
import Compact.Completion.C981.OutwardAnchor
import Compact.Geometry.ClosedFrames

/-! The sharp NW point of OTHER-GEOMETRY Theorem10. The entire foreign
segment forces a support inequality. Exact unit-vector comparisons replace
the half-angle interval and suffice for the one point needed by the ending. -/
namespace N12Compact.CommonCases.NorthwestSharpPoint
open S12 S12Pilot
set_option Elab.async false

private theorem top_support (q : OpenSquare)
    (fLow : q.loU < q.c*(13/50)+q.s)
    (fHigh : q.c*(13/50)+q.s < q.loU+q.side)
    (fFace : q.loV+q.side ≤ q.c-q.s*(13/50))
    (tFace : q.loU+q.side ≤ q.c*(4/5)+q.s)
    (tLow : q.loV < q.c-q.s*(4/5))
    (tHigh : q.c-q.s*(4/5) < q.loV+q.side)
    (avoid : ∀ x : ℝ, 13/50≤x → x≤4/5 → ¬q.Inside x 1) :
    q.s*(q.loU+q.side)+q.c*(q.loV+q.side) ≤ 1 := by
  let u0 := -(q.c*(4/5)+q.s)
  let v0 := -(q.c-q.s*(4/5))
  let u1 := -(q.c*(13/50)+q.s)
  let v1 := -(q.c-q.s*(13/50))
  have cut := LowerSegmentSupport.support (-(q.loU+q.side)) (-q.loU)
    (-(q.loV+q.side)) (-q.loV) u0 v0 u1 v1
    (by dsimp [u0]; linarith only [tFace])
    (by dsimp [u1]; linarith only [fHigh])
    (by dsimp [u1]; linarith only [fLow])
    (by dsimp [v0]; linarith only [tHigh])
    (by dsimp [v0]; linarith only [tLow])
    (by dsimp [v1]; linarith only [fFace])
    (by
      intro w wn wu own
      apply avoid ((1-w)*(4/5)+w*(13/50))
        (by linarith only [wu]) (by linarith only [wn])
      change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
      dsimp [u0,v0,u1,v1] at own
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  dsimp [u0,v0,u1,v1] at cut
  nlinarith only [cut,q.unit_normal]

theorem positive_points (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0) (missingR : ¬q.Inside 1 0)
    (missingP : ¬q.Inside 1 1)
    (avoid : ∀ x : ℝ, 13/50≤x → x≤4/5 → ¬q.Inside x 1) :
    q.Inside (121/300) (-1/6) ∧ q.Inside (3/5) (-1/10) := by
  classical
  have missingF := avoid (13/50) le_rfl (by norm_num)
  have missingT := avoid (4/5) (by norm_num) le_rfl
  simp only [OpenSquare.Inside,InBands,mul_one,mul_zero,zero_add,add_zero]
    at missingG missingR missingP missingF missingT
  have bounds := CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal
  have cu := bounds.2.1
  have gHighU : q.c*(13/50) < q.loU+q.side := by
    linarith only [marker.2.1,cp,sn]
  have gHighV : -q.s*(13/50) < q.loV+q.side := by
    linarith only [marker.2.2.2,cp,order]
  have gLowV : q.loV < -q.s*(13/50) := by
    by_contra bad
    have face : -q.s*(13/50) ≤ q.loV := by exact le_of_not_gt bad
    have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
      linarith only [outward.2.1,order]
    have fLowV : q.loV < -q.s*(13/50)+q.c := by
      linarith only [marker.2.2.1,cp,sn]
    have fHighV : -q.s*(13/50)+q.c < q.loV+q.side := by
      linarith only [face,side,cu]
    have fFace : q.c*(13/50)+q.s ≤ q.loU :=
      le_of_not_gt (fun own => missingF ⟨own,fHighU,fLowV,fHighV⟩)
    have tLowU : q.loU < q.c*(4/5)+q.s := by
      linarith only [marker.1,cp,sn]
    have tLowV : q.loV < -q.s*(4/5)+q.c := by
      linarith only [marker.2.2.1,cp,order]
    have tHighV : -q.s*(4/5)+q.c < q.loV+q.side := by
      linarith only [face,side,cu,sn]
    have tFace : q.loU+q.side ≤ q.c*(4/5)+q.s :=
      le_of_not_gt (fun own => missingT ⟨tLowU,own,tLowV,tHighV⟩)
    linarith only [fFace,tFace,side,cu]
  have gFace : q.c*(13/50) ≤ q.loU :=
    le_of_not_gt (fun own => missingG ⟨own,gHighU,gLowV,gHighV⟩)
  have rLowU : q.loU < q.c := by linarith only [marker.1,cp,order]
  have rHighU : q.c < q.loU+q.side := by linarith only [gFace,side,cu]
  have rHighV : -q.s < q.loV+q.side := by linarith only [outward.2.2.2,cp]
  have rFace : -q.s ≤ q.loV :=
    le_of_not_gt (fun own => missingR ⟨rLowU,rHighU,own,rHighV⟩)
  have pLowU : q.loU < q.c+q.s := by linarith only [marker.1,cp,sn]
  have pLowV : q.loV < -q.s+q.c := by linarith only [marker.2.2.1,order]
  have pHighV : -q.s+q.c < q.loV+q.side := by linarith only [rFace,side,cu]
  have pFace : q.loU+q.side ≤ q.c+q.s :=
    le_of_not_gt (fun own => missingP ⟨pLowU,own,pLowV,pHighV⟩)
  have fLowU : q.loU < q.c*(13/50)+q.s := by linarith only [pFace,side,cu]
  have fHighU : q.c*(13/50)+q.s < q.loU+q.side := by
    linarith only [outward.2.1,order]
  have fLowV : q.loV < -q.s*(13/50)+q.c := by
    linarith only [marker.2.2.1,cp,sn]
  have fFace : q.loV+q.side ≤ -q.s*(13/50)+q.c :=
    le_of_not_gt (fun own => missingF ⟨fLowU,fHighU,fLowV,own⟩)
  have tLowU : q.loU < q.c*(4/5)+q.s := by linarith only [marker.1,cp,sn]
  have tLowV : q.loV < -q.s*(4/5)+q.c := by linarith only [marker.2.2.1,cp,order]
  have tFace : q.loV+q.side ≤ -q.s*(4/5)+q.c := by
    by_contra bad
    have tHighV : -q.s*(4/5)+q.c < q.loV+q.side := by exact lt_of_not_ge bad
    have tUpperU : q.loU+q.side ≤ q.c*(4/5)+q.s :=
      le_of_not_gt (fun own => missingT ⟨tLowU,own,tLowV,tHighV⟩)
    have support := top_support q fLowU fHighU (by linarith only [fFace]) tUpperU
      (by linarith only [tLowV]) (by linarith only [tHighV]) avoid
    have one := mul_nonneg sn (sub_nonneg.mpr gFace)
    have two := mul_nonneg cp.le (show 0 ≤ q.loV+q.s by linarith only [rFace])
    have strict := mul_pos (sub_pos.mpr side)
      (show 0 < q.c+q.s by linarith only [cp,sn])
    have cross := mul_nonneg cp.le sn
    nlinarith only [support,one,two,strict,bounds.2.2.2.2,cross]
  have upperSpan : 1 < q.c+(1/5)*q.s := by linarith only [rFace,tFace,side]
  have upperAngle : (12/13)*q.s < (5/13)*q.c := by
    by_contra bad
    have short := CanonicalProjection.after q.c q.s (12/13) (5/13) 1 (1/5)
      q.unit_normal (by norm_num) (by exact le_of_not_gt bad) (by norm_num) (by norm_num)
    norm_num at short
    linarith only [upperSpan,short]
  have lowerSpan : 1 < (37/50)*q.c+q.s := by linarith only [gFace,pFace,side]
  have lowerAngle : (1131/3869)*q.c < (3700/3869)*q.s := by
    by_contra bad
    have short := CanonicalProjection.before q.c q.s (3700/3869) (1131/3869) (37/50) 1
      q.unit_normal (by norm_num) (by exact le_of_not_gt bad) (by norm_num) (by norm_num)
    norm_num at short
    linarith only [lowerSpan,short]
  have lowU := CanonicalProjection.before q.c q.s (12/13) (5/13) (179/300) (7/6)
    q.unit_normal (by norm_num) upperAngle.le (by norm_num) (by norm_num)
  have lowV := CanonicalProjection.after q.c q.s (3700/3869) (1131/3869) (7/6) (-119/300)
    q.unit_normal (by norm_num) lowerAngle.le (by norm_num) (by norm_num)
  norm_num at lowU lowV
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · linarith only [pFace,side,lowU]
    · linarith only [outward.2.1,cp,sn]
    · linarith only [tFace,side,lowV]
    · linarith only [marker.2.2.2,cp,sn]
  · have lowU' := CanonicalProjection.before q.c q.s (12/13) (5/13) (2/5) (11/10)
      q.unit_normal (by norm_num) upperAngle.le (by norm_num) (by norm_num)
    have lowV' := CanonicalProjection.after q.c q.s (3700/3869) (1131/3869) (11/10) (-1/5)
      q.unit_normal (by norm_num) lowerAngle.le (by norm_num) (by norm_num)
    norm_num at lowU' lowV'
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [pFace,side,lowU']
    · linarith only [outward.2.1,cp,sn]
    · linarith only [tFace,side,lowV']
    · linarith only [marker.2.2.2,cp,sn]

theorem positive_point (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (marker : q.Inside (7/20) (7/20)) (outward : q.Inside 1 (13/50))
    (missingG : ¬q.Inside (13/50) 0) (missingR : ¬q.Inside 1 0)
    (missingP : ¬q.Inside 1 1)
    (avoid : ∀ x : ℝ, 13/50≤x → x≤4/5 → ¬q.Inside x 1) :
    q.Inside (121/300) (-1/6) :=
  (positive_points q side cp sn order marker outward missingG missingR missingP avoid).1

private noncomputable def chart (q : OpenSquare) : OpenSquare where
  c := q.c
  s := q.s
  loU := q.loV-2*q.c+2*q.s
  loV := -q.loU-q.side+2*q.c+2*q.s
  side := q.side
  unit_normal := q.unit_normal
  side_pos := q.side_pos

private theorem inside_chart (q : OpenSquare) (x y : ℝ) :
    (chart q).Inside x y ↔ q.Inside (2-y) (2+x) := by
  dsimp [chart,OpenSquare.Inside,InBands]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;>
    nlinarith only [a,b,c,d]

/-- All orientations of the actual NW owner. The two outward anchors and
the whole left-wall segment also discharge its unfavorable sign. -/
theorem points_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (33/20) (47/20))
    (outward : q.Inside (8/5) 3) (elbow : q.Inside (87/50) 3)
    (missingG : ¬q.Inside 2 (113/50)) (missingR : ¬q.Inside 2 3)
    (missingP : ¬q.Inside 1 3) (missingT : ¬q.Inside 2 (1543/500))
    (avoid : ∀ z : ℝ, 113/50≤z → z≤14/5 → ¬q.Inside 1 z) :
    q.Inside (13/6) (721/300) ∧ q.Inside (21/10) (13/5) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m := (same _ _).mpr marker
  have a := (same _ _).mpr outward
  have e := (same _ _).mpr elbow
  have g : ¬r.Inside 2 (113/50) := fun h => missingG ((same _ _).mp h)
  have rr : ¬r.Inside 2 3 := fun h => missingR ((same _ _).mp h)
  have p : ¬r.Inside 1 3 := fun h => missingP ((same _ _).mp h)
  have tt : ¬r.Inside 2 (1543/500) := fun h => missingT ((same _ _).mp h)
  have segment (z : ℝ) (lo : 113/50≤z) (hi : z≤14/5) : ¬r.Inside 1 z :=
    fun h => avoid z lo hi ((same _ _).mp h)
  have sign : 0 < r.s := by
    by_contra bad
    have negative : r.s≤0 := by exact le_of_not_gt bad
    let swapped := turnFrame (turnFrame (turnFrame (pullSwap r)))
    apply C981CompletionOutwardAnchor.nonnegative_impossible swapped side'
      (by simpa [swapped,turnFrame,pullSwap] using cp)
      (by change 0≤-r.s; linarith only [negative])
      (by
        have ord : -r.s≤r.c := by simpa only [abs_of_nonpos negative] using canonical
        simpa [swapped,turnFrame,pullSwap] using ord)
    · simpa [swapped,inside_pullSwap] using m
    · simpa [swapped,inside_pullSwap] using a
    · simpa [swapped,inside_pullSwap] using p
    · simpa [swapped,inside_pullSwap] using tt
    · simpa [swapped,inside_pullSwap] using g
    · intro z lo hi own
      exact segment z lo hi (by simpa [swapped,inside_pullSwap] using own)
  have answer := positive_points (chart r) side' cp sign.le
    (by change r.s≤r.c; simpa only [abs_of_pos sign] using canonical)
    (by apply (inside_chart _ _ _).mpr; convert m using 1 <;> norm_num)
    (by apply (inside_chart _ _ _).mpr; convert e using 1 <;> norm_num)
    (by intro h; apply g; have h' := (inside_chart _ _ _).mp h; norm_num at h'; exact h')
    (by intro h; apply rr; have h' := (inside_chart _ _ _).mp h; norm_num at h'; exact h')
    (by intro h; apply p; have h' := (inside_chart _ _ _).mp h; norm_num at h'; exact h')
    (by
      intro x lo hi h
      apply segment (2+x) (by linarith only [lo]) (by linarith only [hi])
      have h' := (inside_chart _ _ _).mp h
      norm_num at h'
      exact h')
  have first := (inside_chart _ _ _).mp answer.1
  have second := (inside_chart _ _ _).mp answer.2
  norm_num at first second
  exact ⟨(same _ _).mp first,(same _ _).mp second⟩

theorem point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (33/20) (47/20))
    (outward : q.Inside (8/5) 3) (elbow : q.Inside (87/50) 3)
    (missingG : ¬q.Inside 2 (113/50)) (missingR : ¬q.Inside 2 3)
    (missingP : ¬q.Inside 1 3) (missingT : ¬q.Inside 2 (1543/500))
    (avoid : ∀ z : ℝ, 113/50≤z → z≤14/5 → ¬q.Inside 1 z) :
    q.Inside (13/6) (721/300) :=
  (points_original q side marker outward elbow missingG missingR missingP missingT avoid).1

/-- The same whole-wall argument also supplies a point higher on the inward side. -/
theorem upper_point_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (33/20) (47/20))
    (outward : q.Inside (8/5) 3) (elbow : q.Inside (87/50) 3)
    (missingG : ¬q.Inside 2 (113/50)) (missingR : ¬q.Inside 2 3)
    (missingP : ¬q.Inside 1 3) (missingT : ¬q.Inside 2 (1543/500))
    (avoid : ∀ z : ℝ, 113/50≤z → z≤14/5 → ¬q.Inside 1 z) :
    q.Inside (21/10) (13/5) :=
  (points_original q side marker outward elbow missingG missingR missingP missingT avoid).2

#print axioms point_original
end N12Compact.CommonCases.NorthwestSharpPoint
