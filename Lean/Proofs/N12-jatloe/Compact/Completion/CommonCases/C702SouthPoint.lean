import Compact.Completion.CommonCases.C702SouthScalars
import Compact.Completion.CommonCases.LowerSegmentSupport
import Compact.Completion.CommonCases.OutwardScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! The southwest closing point of C702. The complete genuine foreign
K--R segment is retained, with its support derived from a corner crossing. -/
namespace N12Compact.CommonCases.C702SouthPoint
open S12 S12Pilot
set_option Elab.async false

private def Avoid (q : OpenSquare) : Prop :=
  ∀ w : ℝ, 0≤w → w≤1 → ¬q.Inside
    ((1-w)*(41/20)+w*(47/20)) ((1-w)*(41/20)+w*(33/20))

theorem positive_faces (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (m : q.Inside (33/20) (33/20)) (p : q.Inside 2 (87/50))
    (d : q.Inside (87/50) 2)
    (missingL : ¬q.Inside 1 (33/20)) (missingB : ¬q.Inside (33/20) 1)
    (missingN : ¬q.Inside (33/20) (47/20)) (missingR : ¬q.Inside (47/20) (33/20)) :
    q.c+q.s*(33/20) ≤ q.loU ∧ -q.s*(33/20)+q.c ≤ q.loV := by
  classical
  simp only [OpenSquare.Inside,InBands,mul_one] at missingL missingB
  have bHighU : q.c*(33/20)+q.s < q.loU+q.side := by linarith only [m.2.1,sn]
  have bHighV : -q.s*(33/20)+q.c < q.loV+q.side := by linarith only [m.2.2.2,cp]
  have bFace : -q.s*(33/20)+q.c ≤ q.loV := by
    by_contra bad
    have bLowV := by exact lt_of_not_ge bad
    have bLowFace : q.c*(33/20)+q.s ≤ q.loU :=
      le_of_not_gt (fun own => missingB ⟨own,bHighU,bLowV,bHighV⟩)
    have nLowU : q.loU < q.c*(33/20)+q.s*(47/20) := by linarith only [m.1,sn]
    have nLowV : q.loV < -q.s*(33/20)+q.c*(47/20) := by linarith only [m.2.2.1,cp]
    have shortN := OutwardScalars.increasing_projection q.c q.s 0 (27/20)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    have nHighU : q.c*(33/20)+q.s*(47/20) < q.loU+q.side := by
      linarith only [bLowFace,side,shortN]
    have nFace : q.loV+q.side ≤ -q.s*(33/20)+q.c*(47/20) :=
      le_of_not_gt (fun own => missingN ⟨nLowU,nHighU,nLowV,own⟩)
    have rLowU : q.loU < q.c*(47/20)+q.s*(33/20) := by linarith only [m.1,cp]
    have rHighV : -q.s*(47/20)+q.c*(33/20) < q.loV+q.side := by
      linarith only [d.2.2.2,cp,sn]
    have shortR := short_projections q (7/10) (13/20) (by norm_num)
    have rHighU : q.c*(47/20)+q.s*(33/20) < q.loU+q.side := by
      linarith only [bLowFace,side,shortR.2.1]
    have rFace : -q.s*(47/20)+q.c*(33/20) ≤ q.loV :=
      le_of_not_gt (fun own => missingR ⟨rLowU,rHighU,own,rHighV⟩)
    have short := OutwardScalars.increasing_projection q.c q.s (7/10) (7/10)
      cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
    linarith only [nFace,rFace,short,side]
  have lHighU : q.c+q.s*(33/20) < q.loU+q.side := by linarith only [m.2.1,cp]
  have lLowV : q.loV < -q.s+q.c*(33/20) := by linarith only [m.2.2.1,sn]
  have short := OutwardScalars.increasing_projection q.c q.s (13/20) (13/20)
    cp sn order q.unit_normal (by norm_num) (by norm_num) (by norm_num)
  have lHighV : -q.s+q.c*(33/20) < q.loV+q.side := by linarith only [bFace,side,short]
  have lFace : q.c+q.s*(33/20) ≤ q.loU :=
    le_of_not_gt (fun own => missingL ⟨own,lHighU,lLowV,lHighV⟩)
  exact ⟨lFace,bFace⟩

private theorem upper_support (q : OpenSquare)
    (rLowU : q.loU < q.c*(47/20)+q.s*(33/20))
    (rLowV : q.loV < -q.s*(47/20)+q.c*(33/20))
    (rHighV : -q.s*(47/20)+q.c*(33/20) < q.loV+q.side)
    (kLowU : q.loU < q.c*(41/20)+q.s*(41/20))
    (kLowV : q.loV < -q.s*(41/20)+q.c*(41/20)) (avoid : Avoid q) :
    q.loU+q.side ≤ q.c*(41/20)+q.s*(41/20) ∨
      ((4/5)*q.c+(3/5)*q.s)*(q.loU+q.side)+
      ((3/5)*q.c-(4/5)*q.s)*(q.loV+q.side) ≤ 287/100 := by
  classical
  by_cases face : q.loU+q.side ≤ q.c*(41/20)+q.s*(41/20)
  · exact Or.inl face
  have kHighU := lt_of_not_ge face
  have missingR := avoid 1 (by norm_num) (by norm_num)
  have missingK := avoid 0 (by norm_num) (by norm_num)
  norm_num at missingR missingK
  have rFace : q.loU+q.side ≤ q.c*(47/20)+q.s*(33/20) :=
    le_of_not_gt (fun own => missingR ⟨rLowU,own,rLowV,rHighV⟩)
  have kFace : q.loV+q.side ≤ -q.s*(41/20)+q.c*(41/20) :=
    le_of_not_gt (fun own => missingK ⟨kLowU,kHighU,kLowV,own⟩)
  let u0 := -(q.c*(47/20)+q.s*(33/20))
  let v0 := -(-q.s*(47/20)+q.c*(33/20))
  let u1 := -(q.c*(41/20)+q.s*(41/20))
  let v1 := -(-q.s*(41/20)+q.c*(41/20))
  have cut := LowerSegmentSupport.support (-(q.loU+q.side)) (-q.loU)
    (-(q.loV+q.side)) (-q.loV) u0 v0 u1 v1
    (by dsimp [u0]; linarith only [rFace])
    (by dsimp [u1]; linarith only [kHighU])
    (by dsimp [u1]; linarith only [kLowU])
    (by dsimp [v0]; linarith only [rHighV])
    (by dsimp [v0]; linarith only [rLowV])
    (by dsimp [v1]; linarith only [kFace])
    (by
      intro w wn wu own
      apply avoid (1-w) (by linarith only [wu]) (by linarith only [wn])
      change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
      dsimp [u0,v0,u1,v1] at own
      refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [own.1,own.2.1,own.2.2.1,own.2.2.2])
  right
  dsimp [u0,v0,u1,v1] at cut
  nlinarith only [cut,q.unit_normal]

private theorem positive (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (m : q.Inside (33/20) (33/20)) (p : q.Inside 2 (87/50)) (d : q.Inside (87/50) 2)
    (e : q.Inside (3/2) 2) (f : q.Inside 2 (3/2))
    (missingL : ¬q.Inside 1 (33/20)) (missingB : ¬q.Inside (33/20) 1)
    (missingN : ¬q.Inside (33/20) (47/20)) (missingR : ¬q.Inside (47/20) (33/20))
    (avoid : Avoid q) : q.Inside (13/10) (193/100) := by
  classical
  have faces := positive_faces q side cp sn order m p d missingL missingB missingN missingR
  have kLowU : q.loU < q.c*(41/20)+q.s*(41/20) := by linarith only [e.1,cp,sn]
  have kLowV : q.loV < -q.s*(41/20)+q.c*(41/20) := by linarith only [f.2.2.1,cp,order]
  have missingK := avoid 0 (by norm_num) (by norm_num)
  norm_num at missingK
  have lowU : q.loU < q.c*(13/10)+q.s*(193/100) := by
    by_cases steep : q.c ≤ 11*q.s
    · have kHighV : -q.s*(41/20)+q.c*(41/20) < q.loV+q.side := by linarith only [e.2.2.2,steep]
      have face : q.loU+q.side ≤ q.c*(41/20)+q.s*(41/20) :=
        le_of_not_gt (fun own => missingK ⟨kLowU,own,kLowV,kHighV⟩)
      have short := short_projections q (3/4) (3/25) (by norm_num)
      linarith only [face,side,short.2.1]
    · have shallow : 11*q.s < q.c := lt_of_not_ge steep
      have choices := upper_support q
        (by linarith only [m.1,cp])
        (by linarith only [f.2.2.1,shallow,cp])
        (by linarith only [d.2.2.2,cp,sn]) kLowU kLowV avoid
      rcases choices with face | support
      · have short := short_projections q (3/4) (3/25) (by norm_num)
        linarith only [face,side,short.2.1]
      · by_contra bad
        have face : q.c*(13/10)+q.s*(193/100) ≤ q.loU := by exact le_of_not_gt bad
        let α := (4/5)*q.c+(3/5)*q.s
        let β := (3/5)*q.c-(4/5)*q.s
        have ap : 0 < α := by dsimp [α]; linarith only [cp,sn]
        have bp : 0 < β := by dsimp [β]; linarith only [shallow,cp]
        have uWeighted := mul_pos ap (show 0 < q.loU+q.side-(q.c*(13/10)+q.s*(193/100)+1)
          by linarith only [face,side])
        have vWeighted := mul_pos bp (show 0 < q.loV+q.side-(-q.s*(3/2)+q.c*2)
          by linarith only [e.2.2.2])
        have margin := C702SouthScalars.shallow_margin q.c q.s cp sn q.unit_normal shallow
        dsimp [α,β] at uWeighted vWeighted
        nlinarith only [support,uWeighted,vWeighted,q.unit_normal,margin]
  have shortV := short_projections q (-7/20) (93/100) (by norm_num)
  refine ⟨lowU,?_,?_,?_⟩
  · linarith only [e.2.1,cp,sn]
  · linarith only [f.2.2.1,cp,sn]
  · linarith only [faces.2,side,shortV.2.2.2]

private theorem negative (q : OpenSquare) (t : ℝ) (signed : q.s=-t)
    (side : 1 < q.side) (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c)
    (m : q.Inside (33/20) (33/20)) (p : q.Inside 2 (87/50)) (d : q.Inside (87/50) 2)
    (e : q.Inside (3/2) 2) (f : q.Inside 2 (3/2))
    (missingL : ¬q.Inside 1 (33/20)) (missingB : ¬q.Inside (33/20) 1)
    (missingN : ¬q.Inside (33/20) (47/20)) (missingR : ¬q.Inside (47/20) (33/20))
    (avoid : Avoid q) : q.Inside (13/10) (193/100) := by
  classical
  let swapped := turnFrame (turnFrame (turnFrame (pullSwap q)))
  have swappedFaces := positive_faces swapped side
    (by simpa [swapped,turnFrame,pullSwap] using cp)
    (by dsimp [swapped,turnFrame,pullSwap]; rw [signed]; linarith only [tn])
    (by dsimp [swapped,turnFrame,pullSwap]; rw [signed]; linarith only [order])
    (by simpa [swapped,inside_pullSwap] using m)
    (by simpa [swapped,inside_pullSwap] using d)
    (by simpa [swapped,inside_pullSwap] using p)
    (by intro own; apply missingB; simpa [swapped,inside_pullSwap] using own)
    (by intro own; apply missingL; simpa [swapped,inside_pullSwap] using own)
    (by intro own; apply missingR; simpa [swapped,inside_pullSwap] using own)
    (by intro own; apply missingN; simpa [swapped,inside_pullSwap] using own)
  dsimp [swapped,turnFrame,pullSwap] at swappedFaces
  rw [signed] at swappedFaces
  have uFace : q.c-t*(33/20) ≤ q.loU := by linarith only [swappedFaces.2]
  have vFace : t*(33/20)+q.c ≤ q.loV := by linarith only [swappedFaces.1]
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  obtain ⟨cLow,cu,_,_,_⟩ := CanonicalScalars.bounds q.c t cp tn order unit
  have shortR := short_projections q (7/10) (13/20) (by norm_num)
  rw [signed] at shortR
  have choices := upper_support q
    (by have h := m.1; rw [signed] at h ⊢; linarith only [h,cp])
    (by have h := m.2.2.1; rw [signed] at h ⊢; linarith only [h,tn])
    (by rw [signed]; linarith only [vFace,side,shortR.2.2.2])
    (by have h := e.1; rw [signed] at h ⊢; linarith only [h,cp,order])
    (by have h := m.2.2.1; rw [signed] at h ⊢; linarith only [h,cp,tn]) avoid
  rw [signed] at choices
  have lowU : q.loU < q.c*(13/10)+(-t)*(193/100) := by
    rcases choices with face | support
    · linarith only [face,side,cu,tn]
    · by_contra bad
      have face : q.c*(13/10)+(-t)*(193/100) ≤ q.loU := by exact le_of_not_gt bad
      let α := (4/5)*q.c-(3/5)*t
      let β := (3/5)*q.c+(4/5)*t
      have ap : 0 < α := by dsimp [α]; linarith only [cp,order]
      have bp : 0 < β := by dsimp [β]; linarith only [cp,tn]
      have uWeighted := mul_pos ap (show 0 < q.loU+q.side-(q.c*(13/10)-t*(193/100)+1)
        by linarith only [face,side])
      have vWeighted := mul_pos bp (show 0 < q.loV+q.side-(t*(33/20)+q.c+1)
        by linarith only [vFace,side])
      have margin := C702SouthScalars.negative_margin q.c t cp tn order unit
      dsimp [α,β] at uWeighted vWeighted
      nlinarith only [support,uWeighted,vWeighted,unit,margin]
  have lowV : q.loV < t*(13/10)+q.c*(193/100) := by
    rcases choices with face | support
    · have first := f.2.1
      rw [signed] at first
      have shallow : 11*t < q.c := by linarith only [first,face]
      have marker := m.2.2.1
      rw [signed] at marker
      linarith only [marker,shallow,cp]
    · apply lt_of_not_ge
      intro face
      let α := (4/5)*q.c-(3/5)*t
      let β := (3/5)*q.c+(4/5)*t
      have ap : 0 < α := by dsimp [α]; linarith only [cp,order]
      have bp : 0 < β := by dsimp [β]; linarith only [cp,tn]
      have uWeighted := mul_pos ap (show 0 < q.loU+q.side-(q.c-t*(33/20)+1)
        by linarith only [uFace,side])
      have vWeighted := mul_pos bp (show 0 < q.loV+q.side-(t*(13/10)+q.c*(193/100)+1)
        by linarith only [face,side])
      have ct := mul_nonneg cp.le tn
      have margin : 0 < (7/5)*q.c+(1/5)*t+(9/125)*t^2+(101/250)*q.c*t-114/125 := by
        nlinarith only [cLow,tn,ct,sq_nonneg t]
      dsimp [α,β] at uWeighted vWeighted
      nlinarith only [support,uWeighted,vWeighted,unit,margin]
  rw [OpenSquare.Inside,InBands,signed]
  refine ⟨lowU,?_,?_,?_⟩
  · have high := e.2.1
    rw [signed] at high
    linarith only [high,cp,order]
  · linarith only [lowV]
  · have high := d.2.2.2
    rw [signed] at high
    linarith only [high,cp,tn]

theorem point (q : OpenSquare) (side : 1 < q.side)
    (m : q.Inside (33/20) (33/20)) (p : q.Inside 2 (87/50)) (d : q.Inside (87/50) 2)
    (e : q.Inside (3/2) 2) (f : q.Inside 2 (3/2))
    (missingL : ¬q.Inside 1 (33/20)) (missingB : ¬q.Inside (33/20) 1)
    (missingN : ¬q.Inside (33/20) (47/20)) (missingR : ¬q.Inside (47/20) (33/20))
    (avoid : ∀ w : ℝ, 0≤w → w≤1 → ¬q.Inside
      ((1-w)*(41/20)+w*(47/20)) ((1-w)*(41/20)+w*(33/20))) :
    q.Inside (13/10) (193/100) := by
  classical
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have m' := (same _ _).mpr m
  have p' := (same _ _).mpr p
  have d' := (same _ _).mpr d
  have e' := (same _ _).mpr e
  have f' := (same _ _).mpr f
  have l : ¬r.Inside 1 (33/20) := fun own => missingL ((same _ _).mp own)
  have b : ¬r.Inside (33/20) 1 := fun own => missingB ((same _ _).mp own)
  have n : ¬r.Inside (33/20) (47/20) := fun own => missingN ((same _ _).mp own)
  have rr : ¬r.Inside (47/20) (33/20) := fun own => missingR ((same _ _).mp own)
  have segment : Avoid r := fun w wn wu own => avoid w wn wu ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · exact (same _ _).mp (positive r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) m' p' d' e' f' l b n rr segment)
  · exact (same _ _).mp (negative r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical) m' p' d' e' f' l b n rr segment)

#print axioms point
end N12Compact.CommonCases.C702SouthPoint
