import Compact.Completion.CommonCases.SegmentSupport
import Compact.Completion.CommonCases.CanonicalScalars
import Compact.Geometry.ClosedFrames
import S12.ShortCluster

/-! C982's one-segment, three-point obstruction. The one complete foreign
segment is supplied in the final adapter by the actual merged bottom square.
Exterior contact is retained as a weak inequality throughout. -/
namespace N12Compact.CommonCases.C982Obstruction
open S12 S12Pilot
set_option Elab.async false

private def Avoid (q : OpenSquare) : Prop :=
  ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
    ¬ q.Inside ((1-w)*(-7/20)+w*(-1/20))
      ((1-w)*(-92/125)+w*(19/100))

private theorem positive_support (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (origin : q.Inside 0 0) (avoid : Avoid q) :
    (-(1/20)*q.c+(19/100)*q.s ≤ q.loU ∧
      -(7/20)*q.c-(92/125)*q.s ≤ q.loU) ∨
    (463/500*q.c-3/10*q.s)*q.loU-
      (3/10*q.c+463/500*q.s)*(q.loV+q.side) ≥ -(1033/10000) := by
  let u0 := -(7/20)*q.c-(92/125)*q.s
  let v0 := (7/20)*q.s-(92/125)*q.c
  let u1 := -(1/20)*q.c+(19/100)*q.s
  let v1 := (1/20)*q.s+(19/100)*q.c
  have anchor : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa [OpenSquare.Inside,InBands] using origin
  have sp := short_projections q (3/10) (463/500) (by norm_num)
  have du : 0 < u1-u0 := by dsimp [u1,u0]; linarith only [cp,sn]
  have dv : 0 < v1-v0 := by dsimp [v1,v0]; linarith only [cp,order]
  have line : (v1-v0)*u0-(u1-u0)*v0 = -(1033/10000) := by
    calc
      _ = -(1033/10000)*(q.c^2+q.s^2) := by dsimp [u0,v0,u1,v1]; ring
      _ = _ := by rw [q.unit_normal]; ring
  have segment (w : ℝ) (wn : 0 ≤ w) (wu : w ≤ 1) :
      ¬ (q.loU < (1-w)*u0+w*u1 ∧ (1-w)*u0+w*u1 < q.loU+q.side ∧
        q.loV < (1-w)*v0+w*v1 ∧ (1-w)*v0+w*v1 < q.loV+q.side) := by
    intro h
    apply avoid w wn wu
    change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
    convert h using 1 <;> dsimp [u0,v0,u1,v1] <;> ring
  have choices := SegmentSupport.increasing q.loU (q.loU+q.side)
    q.loV (q.loV+q.side) u0 v0 u1 v1 anchor
    (by dsimp [u0]; linarith only [cp,sn])
    (by dsimp [v0]; linarith only [cp,order])
    (by dsimp [v1]; linarith only [cp,sn]) du dv
    (by dsimp [u1,u0]; linarith only [sp.2.1,side])
    (by dsimp [v1,v0]; linarith only [sp.2.2.2,side])
    (by rw [line]; norm_num) segment
  rcases choices with face | support
  · left
    exact ⟨face,by dsimp [u0,u1] at *; linarith only [face,du]⟩
  · right
    rw [line] at support
    convert support using 1 <;> dsimp [u0,v0,u1,v1] <;> ring

private theorem negative_support (q : OpenSquare) (t : ℝ)
    (signed : q.s = -t) (side : 1 < q.side)
    (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c)
    (origin : q.Inside 0 0) (avoid : Avoid q) :
    (-(1/20)*q.c-(19/100)*t ≤ q.loU ∧
      -(7/20)*q.c+(92/125)*t ≤ q.loU) ∨
    ((0 ≤ 463/500*t-3/10*q.c ∧
        (463/500*q.c+3/10*t)*q.loU+
          (463/500*t-3/10*q.c)*q.loV ≥ -(1033/10000)) ∨
      (463/500*t-3/10*q.c < 0 ∧
        (463/500*q.c+3/10*t)*q.loU+
          (463/500*t-3/10*q.c)*(q.loV+q.side) ≥ -(1033/10000))) := by
  let u0 := -(7/20)*q.c+(92/125)*t
  let v0 := -(7/20)*t-(92/125)*q.c
  let u1 := -(1/20)*q.c-(19/100)*t
  let v1 := -(1/20)*t+(19/100)*q.c
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  have anchor : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa [OpenSquare.Inside,InBands] using origin
  have sp := short_projections q (3/10) (463/500) (by norm_num)
  rw [signed] at sp
  have vz : 0 < v1 := by dsimp [v1]; linarith only [cp,order]
  have vb : v0 < 0 := by dsimp [v0]; linarith only [cp,tn]
  have uz : u1 < 0 := by dsimp [u1]; linarith only [cp,tn]
  have dv : 0 < v1-v0 := by dsimp [v1,v0]; linarith only [cp,tn]
  have segment (w : ℝ) (wn : 0 ≤ w) (wu : w ≤ 1) :
      ¬ (q.loU < (1-w)*u0+w*u1 ∧ (1-w)*u0+w*u1 < q.loU+q.side ∧
        q.loV < (1-w)*v0+w*v1 ∧ (1-w)*v0+w*v1 < q.loV+q.side) := by
    intro h
    apply avoid w wn wu
    change q.loU < _ ∧ _ < q.loU+q.side ∧ q.loV < _ ∧ _ < q.loV+q.side
    rw [signed]
    convert h using 1 <;> dsimp [u0,v0,u1,v1] <;> ring
  by_cases zero : u0 = u1
  · have face := SegmentSupport.vertical q.loU (q.loU+q.side) q.loV
      (q.loV+q.side) u0 v0 u1 v1 anchor zero.symm
      (by simpa only [zero] using uz) vb vz segment
    exact Or.inl ⟨by simpa only [zero] using face,face⟩
  by_cases down : u1 < u0
  · have line : (v1-v0)*u0+(u0-u1)*v0 = -(1033/10000) := by
      calc
        _ = -(1033/10000)*(q.c^2+t^2) := by dsimp [u0,v0,u1,v1]; ring
        _ = _ := by rw [unit]; ring
    have choices := SegmentSupport.decreasing q.loU (q.loU+q.side)
      q.loV (q.loV+q.side) u0 v0 u1 v1 anchor uz vb vz
      (by linarith only [down]) dv
      (by dsimp [u0,u1]; linarith only [sp.1,side])
      (by dsimp [v0,v1]; linarith only [sp.2.2.2,side])
      (by rw [line]; norm_num) segment
    rcases choices with face | support
    · left
      exact ⟨by dsimp [u0,u1] at down face ⊢; linarith only [down,face],face⟩
    · right; left
      refine ⟨by dsimp [u0,u1] at down; linarith only [down],?_⟩
      rw [line] at support
      convert support using 1 <;> dsimp [u0,v0,u1,v1] <;> ring
  · have up : u0 < u1 := by rcases lt_or_gt_of_ne zero with h | h; exact h; exact (down h).elim
    have line : (v1-v0)*u0-(u1-u0)*v0 = -(1033/10000) := by
      calc
        _ = -(1033/10000)*(q.c^2+t^2) := by dsimp [u0,v0,u1,v1]; ring
        _ = _ := by rw [unit]; ring
    have choices := SegmentSupport.increasing q.loU (q.loU+q.side)
      q.loV (q.loV+q.side) u0 v0 u1 v1 anchor
      (by linarith only [up,uz]) vb vz (by linarith only [up]) dv
      (by dsimp [u0,u1]; linarith only [sp.2.1,side])
      (by dsimp [v0,v1]; linarith only [sp.2.2.2,side])
      (by rw [line]; norm_num) segment
    rcases choices with face | support
    · left
      exact ⟨face,by dsimp [u0,u1] at up face ⊢; linarith only [up,face]⟩
    · right; right
      refine ⟨by dsimp [u0,u1] at up; linarith only [up],?_⟩
      rw [line] at support
      convert support using 1 <;> dsimp [u0,v0,u1,v1] <;> ring

private theorem positive_impossible (q : OpenSquare) (side : 1 < q.side)
    (cp : 0 < q.c) (sn : 0 ≤ q.s) (order : q.s ≤ q.c)
    (origin : q.Inside 0 0)
    (missingH : ¬q.Inside (92/125) (-13/20))
    (missingR : ¬q.Inside (92/125) (7/20)) (avoid : Avoid q) : False := by
  obtain ⟨clow,cu,_,_,_⟩ := CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal
  have anchor : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa [OpenSquare.Inside,InBands] using origin
  obtain face | support := positive_support q side cp sn order origin avoid
  · have slope : 19*q.s < 5*q.c := by linarith only [face.1,anchor.1]
    have hLowU : q.loU < q.c*(92/125)+q.s*(-13/20) := by
      linarith only [anchor.1,cp,order]
    have hHighU : q.c*(92/125)+q.s*(-13/20) < q.loU+q.side := by
      linarith only [face.1,side,cu,sn]
    have hHighV : -q.s*(92/125)+q.c*(-13/20) < q.loV+q.side := by
      linarith only [anchor.2.2.2,cp,sn]
    have hFace : -q.s*(92/125)+q.c*(-13/20) ≤ q.loV :=
      le_of_not_gt (fun h => missingH ⟨hLowU,hHighU,h,hHighV⟩)
    apply missingR
    refine ⟨?_,?_,?_,?_⟩
    · linarith only [anchor.1,cp,sn]
    · linarith only [face.1,side,cu,order,sn]
    · linarith only [anchor.2.2.1,slope,cp]
    · linarith only [hFace,side,cu]
  · let α := (463/500)*q.c-(3/10)*q.s
    let β := (3/10)*q.c+(463/500)*q.s
    have alphaLow : 2191/5000 < α := by dsimp [α]; linarith only [clow,order]
    have betaLow : 21/100 < β := by dsimp [β]; linarith only [clow,sn]
    have ap : 0 < α := (by norm_num : (0:ℝ) < 2191/5000).trans alphaLow
    have bp : 0 < β := (by norm_num : (0:ℝ) < 21/100).trans betaLow
    have support' : -(1033/10000) ≤ α*q.loU-β*(q.loV+q.side) := support
    have negU : α*(-q.loU) < 1033/10000 := by
      have high := mul_pos bp anchor.2.2.2
      dsimp [α,β] at support' high ⊢
      nlinarith only [support',high]
    have highV : β*(q.loV+q.side) < 1033/10000 := by
      have low := mul_neg_of_pos_of_neg ap anchor.1
      dsimp [α,β] at support' low ⊢
      nlinarith only [support',low]
    have hLowU : q.loU < q.c*(92/125)+q.s*(-13/20) := by
      linarith only [anchor.1,cp,order]
    have hHighV : -q.s*(92/125)+q.c*(-13/20) < q.loV+q.side := by
      linarith only [anchor.2.2.2,cp,sn]
    have hHighU : q.c*(92/125)+q.s*(-13/20) < q.loU+q.side := by
      by_contra failed
      have failed' := le_of_not_gt failed
      have lo : 33/125 < -q.loU := by linarith only [failed',side,cu,sn]
      have big : (2191/5000)*(33/125) < α*(-q.loU) :=
        mul_lt_mul alphaLow lo.le (by norm_num) ap.le
      dsimp [α] at big negU
      linarith only [big,negU]
    have hFace : -q.s*(92/125)+q.c*(-13/20) ≤ q.loV :=
      le_of_not_gt (fun h => missingH ⟨hLowU,hHighU,h,hHighV⟩)
    have rLowU : q.loU < q.c*(92/125)+q.s*(7/20) := by
      linarith only [anchor.1,cp,sn]
    have rHighV : -q.s*(92/125)+q.c*(7/20) < q.loV+q.side := by
      linarith only [hFace,side,cu]
    have rLowV : q.loV < -q.s*(92/125)+q.c*(7/20) := by
      by_contra failed
      have failed' := le_of_not_gt failed
      have lo : 307/500 < q.loV+q.side := by
        linarith only [failed',side,cu,order,sn]
      have big : (21/100)*(307/500) < β*(q.loV+q.side) :=
        mul_lt_mul betaLow lo.le (by norm_num) bp.le
      dsimp [β] at big highV
      linarith only [big,highV]
    have rFace : q.loU+q.side ≤ q.c*(92/125)+q.s*(7/20) :=
      le_of_not_gt (fun h => missingR ⟨rLowU,h,rLowV,rHighV⟩)
    have weightedU := mul_nonneg ap.le (sub_nonneg.mpr rFace)
    have weightedV := mul_nonneg bp.le (sub_nonneg.mpr hFace)
    have combined : q.side*(α+β) ≤
        α*(q.c*(92/125)+q.s*(7/20))-
          β*(-q.s*(92/125)+q.c*(-13/20))+1033/10000 := by
      nlinarith only [support',weightedU,weightedV]
    have identity :
        α*(q.c*(92/125)+q.s*(7/20))-
          β*(-q.s*(92/125)+q.c*(-13/20))+1033/10000 =
        244959/250000-(3/10)*q.s^2+(463/500)*q.c*q.s := by
      dsimp [α,β]
      linear_combination (109567/125000)*q.unit_normal
    rw [identity] at combined
    have margin := CanonicalScalars.positive_margin q.c q.s cp sn order q.unit_normal
    have extra := mul_pos (sub_pos.mpr side)
      (show 0 < α+β by linarith only [ap,bp])
    dsimp [α,β] at combined extra
    nlinarith only [combined,margin,extra]

private theorem negative_impossible (q : OpenSquare) (t : ℝ)
    (signed : q.s = -t) (side : 1 < q.side)
    (cp : 0 < q.c) (tn : 0 ≤ t) (order : t ≤ q.c)
    (origin : q.Inside 0 0)
    (missingP : ¬q.Inside (13/20) (-13/20))
    (missingH : ¬q.Inside (92/125) (-13/20))
    (missingR : ¬q.Inside (92/125) (7/20)) (avoid : Avoid q) : False := by
  have unit : q.c^2+t^2=1 := by simpa only [signed,neg_sq] using q.unit_normal
  obtain ⟨clow,cu,_,_,_⟩ := CanonicalScalars.bounds q.c t cp tn order unit
  have anchor : q.loU < 0 ∧ 0 < q.loU+q.side ∧
      q.loV < 0 ∧ 0 < q.loV+q.side := by
    simpa [OpenSquare.Inside,InBands] using origin
  let uh := (92/125)*q.c+(13/20)*t
  let vh := (92/125)*t-(13/20)*q.c
  let ur := (92/125)*q.c-(7/20)*t
  let vr := (92/125)*t+(7/20)*q.c
  let up := (13/20)*(q.c+t)
  let vp := (13/20)*(t-q.c)
  have hMissing : ¬ (q.loU < uh ∧ uh < q.loU+q.side ∧
      q.loV < vh ∧ vh < q.loV+q.side) := by
    intro h; apply missingH
    dsimp [OpenSquare.Inside,InBands]; rw [signed]
    convert h using 1 <;> dsimp [uh,vh] <;> ring
  have rMissing : ¬ (q.loU < ur ∧ ur < q.loU+q.side ∧
      q.loV < vr ∧ vr < q.loV+q.side) := by
    intro h; apply missingR
    dsimp [OpenSquare.Inside,InBands]; rw [signed]
    convert h using 1 <;> dsimp [ur,vr] <;> ring
  have pMissing : ¬ (q.loU < up ∧ up < q.loU+q.side ∧
      q.loV < vp ∧ vp < q.loV+q.side) := by
    intro h; apply missingP
    dsimp [OpenSquare.Inside,InBands]; rw [signed]
    convert h using 1 <;> dsimp [up,vp] <;> ring
  have rLowU : q.loU < ur := by dsimp [ur]; linarith only [anchor.1,cp,order]
  have rLowV : q.loV < vr := by dsimp [vr]; linarith only [anchor.2.2.1,cp,tn]
  have hLowU : q.loU < uh := by dsimp [uh]; linarith only [anchor.1,cp,tn]
  have pLowU : q.loU < up := by dsimp [up]; linarith only [anchor.1,cp,tn]
  have pHighV : vp < q.loV+q.side := by
    dsimp [vp]; linarith only [anchor.2.2.2,order]
  obtain face | normal := negative_support q t signed side cp tn order origin avoid
  · have slope : 736*t < 350*q.c := by linarith only [face.2,anchor.1]
    have rHighU : ur < q.loU+q.side := by
      dsimp [ur]; linarith only [face.1,side,cu,tn]
    have rFace : q.loV+q.side ≤ vr :=
      le_of_not_gt (fun h => rMissing ⟨rLowU,rHighU,rLowV,h⟩)
    have hHighV : vh < q.loV+q.side := by
      dsimp [vh]; linarith only [anchor.2.2.2,slope,cp]
    have hLowV : q.loV < vh := by
      dsimp [vh,vr] at *
      linarith only [rFace,side,cu]
    have hFace : q.loU+q.side ≤ uh :=
      le_of_not_gt (fun h => hMissing ⟨hLowU,h,hLowV,hHighV⟩)
    have pHighU : up < q.loU+q.side := by
      dsimp [up]; linarith only [face.2,side,cu,tn]
    have pFace : vp ≤ q.loV :=
      le_of_not_gt (fun h => pMissing ⟨pLowU,pHighU,h,pHighV⟩)
    by_cases steep : q.c ≤ 5*t
    · have short := CanonicalScalars.c_small_sine q.c t cp tn unit steep
      dsimp [vr,vp] at rFace pFace
      linarith only [rFace,pFace,short,side]
    · have shallow : 5*t ≤ q.c := (lt_of_not_ge steep).le
      dsimp [uh] at hFace
      linarith only [hFace,face.1,side,cu,shallow]
  · let α := (463/500)*q.c+(3/10)*t
    let γ := (463/500)*t-(3/10)*q.c
    have alphaLow : 3241/5000 < α := by dsimp [α]; linarith only [clow,tn]
    have ap : 0 < α := (by norm_num : (0:ℝ) < 3241/5000).trans alphaLow
    have normal' : (0 ≤ γ ∧ -(1033/10000) ≤ α*q.loU+γ*q.loV) ∨
        (γ < 0 ∧ -(1033/10000) ≤ α*q.loU+γ*(q.loV+q.side)) := normal
    have negU : α*(-q.loU) ≤ 1033/10000 := by
      rcases normal' with ⟨gn,support⟩ | ⟨gp,support⟩
      · have low := mul_nonpos_of_nonneg_of_nonpos gn anchor.2.2.1.le
        dsimp [α,γ] at support low ⊢
        nlinarith only [support,low]
      · have high := mul_neg_of_neg_of_pos gp anchor.2.2.2
        dsimp [α,γ] at support high ⊢
        nlinarith only [support,high]
    have rHighU : ur < q.loU+q.side := by
      by_contra failed
      have failed' := le_of_not_gt failed
      have lo : 33/125 < -q.loU := by
        dsimp [ur] at failed'
        linarith only [failed',side,cu,tn]
      have big : (3241/5000)*(33/125) < α*(-q.loU) :=
        mul_lt_mul alphaLow lo.le (by norm_num) ap.le
      dsimp [α] at big negU
      linarith only [big,negU]
    have rFace : q.loV+q.side ≤ vr :=
      le_of_not_gt (fun h => rMissing ⟨rLowU,rHighU,rLowV,h⟩)
    rcases normal' with ⟨gn,support⟩ | ⟨gp,support⟩
    · have slope : q.c ≤ 5*t := by dsimp [γ] at gn; linarith only [gn,cp]
      have short := CanonicalScalars.c_small_sine q.c t cp tn unit slope
      have pLowV : q.loV < vp := by
        dsimp [vr,vp] at *
        linarith only [rFace,side,short]
      have pFace : q.loU+q.side ≤ up :=
        le_of_not_gt (fun h => pMissing ⟨pLowU,h,pLowV,pHighV⟩)
      have weightedU := mul_nonneg ap.le (sub_nonneg.mpr pFace)
      have weightedV := mul_nonneg gn (sub_nonneg.mpr rFace)
      have combined : q.side*(α+γ) ≤ α*up+γ*vr+1033/10000 := by
        dsimp [α,γ,up,vr] at support weightedU weightedV ⊢
        nlinarith only [support,weightedU,weightedV]
      have identity : α*up+γ*vr+1033/10000 =
          3001/5000+(94909/250000)*t^2+(4501/5000)*q.c*t := by
        dsimp [α,γ,up,vr]
        linear_combination (4969/10000)*unit
      rw [identity] at combined
      have margin := CanonicalScalars.negative_margin q.c t cp tn order unit
      have extra := mul_pos (sub_pos.mpr side)
        (show 0 < α+γ by linarith only [ap,gn])
      dsimp [α,γ] at combined extra
      nlinarith only [combined,margin,extra]
    · have slope : 3*t < q.c := by dsimp [γ] at gp; linarith only [gp,cp]
      have hHighV : vh < q.loV+q.side := by
        dsimp [vh]; linarith only [anchor.2.2.2,slope,cp]
      have hLowV : q.loV < vh := by
        dsimp [vh,vr] at *
        linarith only [rFace,side,cu]
      have hFace : q.loU+q.side ≤ uh :=
        le_of_not_gt (fun h => hMissing ⟨hLowU,h,hLowV,hHighV⟩)
      by_cases shallow : 5*t ≤ q.c
      · have ratio := mul_nonneg (show 0 ≤ q.c-5*t by linarith only [shallow])
          (show 0 ≤ q.c+5*t by linarith only [cp,tn])
        have cLow : 49/50 < q.c := by nlinarith only [unit,ratio,cp]
        have aLow : 9/10 < α := by dsimp [α]; linarith only [cLow,tn]
        have uhHigh : uh ≤ 433/500 := by dsimp [uh]; linarith only [cu,shallow]
        have lo : 67/500 < -q.loU := by
          dsimp [uh] at hFace uhHigh
          linarith only [hFace,side,uhHigh]
        have big : (9/10)*(67/500) < α*(-q.loU) :=
          mul_lt_mul aLow lo.le (by norm_num) ap.le
        dsimp [α] at big negU
        linarith only [big,negU]
      · have steep : q.c ≤ 5*t := (lt_of_not_ge shallow).le
        have short := CanonicalScalars.c_small_sine q.c t cp tn unit steep
        have pLowV : q.loV < vp := by
          dsimp [vr,vp] at *
          linarith only [rFace,side,short]
        have pFace : q.loU+q.side ≤ up :=
          le_of_not_gt (fun h => pMissing ⟨pLowU,h,pLowV,pHighV⟩)
        have ratio := mul_nonneg
          (show 0 ≤ q.c-3*t by linarith only [slope])
          (show 0 ≤ q.c+3*t by linarith only [cp,tn])
        have cLow : 9/10 < q.c := by nlinarith only [unit,ratio,cp]
        have aLow : 4167/5000 < α := by dsimp [α]; linarith only [cLow,tn]
        have upHigh : up < 13/15 := by dsimp [up]; linarith only [cu,slope]
        have lo : 2/15 < -q.loU := by linarith only [pFace,side,upHigh]
        have big : (4167/5000)*(2/15) < α*(-q.loU) :=
          mul_lt_mul aLow lo.le (by norm_num) ap.le
        dsimp [α] at big negU
        linarith only [big,negU]

/-- Every square orientation is excluded, including canonical-axis and
diagonal endpoints. The complete segment is an actual geometric premise. -/
theorem impossible (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside 0 0)
    (missingP : ¬q.Inside (13/20) (-13/20))
    (missingH : ¬q.Inside (92/125) (-13/20))
    (missingR : ¬q.Inside (92/125) (7/20))
    (avoid : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      ¬ q.Inside ((1-w)*(-7/20)+w*(-1/20))
        ((1-w)*(-92/125)+w*(19/100))) : False := by
  obtain ⟨r,cp,canonical,shape,same,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1 < r.side := by simpa only [shape] using side
  have marker' := (same 0 0).mpr marker
  have p : ¬r.Inside (13/20) (-13/20) := fun h => missingP ((same _ _).mp h)
  have h : ¬r.Inside (92/125) (-13/20) := fun h => missingH ((same _ _).mp h)
  have k : ¬r.Inside (92/125) (7/20) := fun h => missingR ((same _ _).mp h)
  have segment : Avoid r := by
    intro w wn wu own
    exact avoid w wn wu ((same _ _).mp own)
  by_cases sign : 0 ≤ r.s
  · exact positive_impossible r side' cp sign
      (by simpa only [abs_of_nonneg sign] using canonical) marker' h k segment
  · exact negative_impossible r (-r.s) (by ring) side' cp
      (by linarith only [sign])
      (by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical)
      marker' p h k segment

theorem impossible_original (q : OpenSquare) (side : 1 < q.side)
    (marker : q.Inside (47/20) (33/20))
    (missingP : ¬q.Inside 3 1)
    (missingH : ¬q.Inside (1543/500) 1)
    (missingR : ¬q.Inside (1543/500) 2)
    (avoid : ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      ¬ q.Inside ((1-w)*2+w*(23/10))
        ((1-w)*(457/500)+w*(46/25))) : False := by
  apply impossible (q.translated (47/20) (33/20)) side
    (by norm_num [inside_translated_iff]; exact marker)
    (by norm_num [inside_translated_iff]; exact missingP)
    (by norm_num [inside_translated_iff]; exact missingH)
    (by norm_num [inside_translated_iff]; exact missingR)
  intro w wn wu own
  apply avoid w wn wu
  have original := (inside_translated_iff _ _ _ _ _).mp own
  convert original using 1 <;> ring

#print axioms impossible_original
end N12Compact.CommonCases.C982Obstruction
