import Compact.Geometry.ClosedFrames
import Compact.Completion.CommonCases.CanonicalScalars
import S12.Convex

/-! The literal two-short-chord specialization used in Theorem 1 of
`C1092-MPPM-ORDINARY-CENTRAL-REDUCTION.md`. The underlying completed proof
is OTHER-GEOMETRY Theorem 3, at r=.65 and heights .74,.65.

The short-chord face consequences are written directly as band inequalities.
An intersection of three open intervals proves the upper support bound from
the whole omitted bar. That bound is derived here, never an input wall.
Reflection exchanges both anchors and all omitted data simultaneously.
All source is uncompiled; no numerical certificates are used. -/
namespace N12Compact.Completion.OtherCases.OrdinaryCentralReduction
open S12 S12Pilot
set_option Elab.async false
noncomputable section

private theorem common_interval (a b c d e f : ℝ)
    (ad : a<d) (ae : a<e) (af : a<f)
    (bd : b<d) (be : b<e) (bf : b<f)
    (cd : c<d) (ce : c<e) (cf : c<f) :
    ∃ x,a<x ∧ b<x ∧ c<x ∧ x<d ∧ x<e ∧ x<f := by
  have gap : max a (max b c)<min d (min e f) :=
    lt_min (max_lt ad (max_lt bd cd))
      (lt_min (max_lt ae (max_lt be ce)) (max_lt af (max_lt bf cf)))
  obtain ⟨x,low,high⟩ := exists_between gap
  exact ⟨x,(le_max_left _ _).trans_lt low,
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt low,
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt low,
    high.trans_le (min_le_left _ _),
    high.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
    high.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The actual upper bar has either a top-vertex support or its right
endpoint's upper transverse face. Neither alternative is postulated. -/
private theorem upper_bar (q : OpenSquare) (h0 h1 : ℝ)
    (cp : 0<q.c) (sp : 0<q.s) (order : q.s≤q.c)
    (h0p : 0<h0) (h0u : h0<1) (h1l : 13/20≤h1) (h1u : h1<1)
    (left : q.Inside 0 h0) (right : q.Inside (13/20) h1)
    (avoid : ∀ x : ℝ,0≤x → x≤13/20 → ¬q.Inside x 1) :
    q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1 ∨
      q.loV+q.side≤q.c-(13/20)*q.s := by
  have height0 := mul_pos cp (sub_pos.mpr h0u)
  have height1 := mul_nonneg sp.le (sub_nonneg.mpr h1l)
  have lowerHeight := mul_pos sp (sub_pos.mpr h0u)
  have lower : q.s*q.loU+q.c*q.loV<1 := by
    have u := mul_lt_mul_of_pos_left left.1 sp
    have v := mul_lt_mul_of_pos_left left.2.2.1 cp
    have identity : q.s*(q.s*h0)+q.c*(q.c*h0)=h0 := by
      linear_combination h0*q.unit_normal
    nlinarith only [u,v,identity,h0u]
  by_contra both
  obtain ⟨topBad,rightBad⟩ := not_or.mp both
  have top := lt_of_not_ge topBad
  have rightHigh := lt_of_not_ge rightBad
  have zeroU : 0<(q.loU+q.side-q.s)/q.c := by
    apply (lt_div_iff₀ cp).mpr
    nlinarith only [right.2.1,height1,order,cp]
  have zeroV : 0<(q.c-q.loV)/q.s := by
    apply (lt_div_iff₀ sp).mpr
    nlinarith only [left.2.2.1,height0]
  have uRight : (q.loU-q.s)/q.c<13/20 := by
    apply (div_lt_iff₀ cp).mpr
    nlinarith only [left.1,lowerHeight,cp]
  have uu : (q.loU-q.s)/q.c<(q.loU+q.side-q.s)/q.c :=
    (div_lt_div_iff_of_pos_right cp).mpr (by linarith only [q.side_pos])
  have uv : (q.loU-q.s)/q.c<(q.c-q.loV)/q.s := by
    apply (div_lt_div_iff₀ cp sp).mpr
    nlinarith only [lower,q.unit_normal]
  have vRight : (q.c-q.loV-q.side)/q.s<13/20 := by
    apply (div_lt_iff₀ sp).mpr
    linarith only [rightHigh]
  have vu : (q.c-q.loV-q.side)/q.s<(q.loU+q.side-q.s)/q.c := by
    apply (div_lt_div_iff₀ sp cp).mpr
    nlinarith only [top,q.unit_normal]
  have vv : (q.c-q.loV-q.side)/q.s<(q.c-q.loV)/q.s :=
    (div_lt_div_iff_of_pos_right sp).mpr (by linarith only [q.side_pos])
  obtain ⟨x,x0,xu,xv,xr,ux,vx⟩ := common_interval 0
    ((q.loU-q.s)/q.c) ((q.c-q.loV-q.side)/q.s) (13/20)
    ((q.loU+q.side-q.s)/q.c) ((q.c-q.loV)/q.s)
    (by norm_num) zeroU zeroV uRight uu uv vRight vu vv
  apply avoid x x0.le xr.le
  have ul := (div_lt_iff₀ cp).mp xu
  have uh := (lt_div_iff₀ cp).mp ux
  have vl := (lt_div_iff₀ sp).mp vx
  have vh := (div_lt_iff₀ sp).mp xv
  refine ⟨?_,?_,?_,?_⟩ <;> linarith only [ul,uh,vl,vh]

/-- Positive canonical implementation of the two-short-chord proof.
The two heights may be exchanged; both literal heights lie in [.65,1). -/
private theorem positive_impossible (q : OpenSquare) (h0 h1 : ℝ)
    (side : 1<q.side) (cp : 0<q.c) (sn : 0≤q.s) (order : q.s≤q.c)
    (h0l : 13/20≤h0) (h0u : h0<1) (h1l : 13/20≤h1) (h1u : h1<1)
    (left : q.Inside 0 h0) (right : q.Inside (13/20) h1)
    (missing0 : ¬q.Inside 0 0) (missingR : ¬q.Inside (13/20) 0)
    (avoid : ∀ x : ℝ,0≤x → x≤13/20 → ¬q.Inside x 1) : False := by
  have bounds := CommonCases.CanonicalScalars.bounds q.c q.s cp sn order q.unit_normal
  have cu := bounds.2.1
  have h0p : 0<h0 := by linarith only [h0l]
  have h1p : 0<h1 := by linarith only [h1l]
  by_cases axis : q.s=0
  · have one : q.c=1 := by nlinarith only [q.unit_normal,axis,cp]
    have own : q.loU<0 ∧ 0<q.loU+q.side ∧ q.loV<h0 ∧ h0<q.loV+q.side := by
      simpa only [OpenSquare.Inside,InBands,axis,one,mul_zero,zero_mul,
        one_mul,neg_zero,zero_add,add_zero] using left
    have lower : 0≤q.loV := by
      apply le_of_not_gt
      intro low
      apply missing0
      simpa only [OpenSquare.Inside,InBands,axis,one,mul_zero,zero_mul,
        one_mul,neg_zero,zero_add,add_zero] using
        And.intro own.1 (And.intro own.2.1 (And.intro low (by linarith only [own.2.2.2,h0p])))
    apply avoid 0 le_rfl (by norm_num)
    simp only [OpenSquare.Inside,InBands,axis,one,mul_zero,zero_mul,
      one_mul,neg_zero,zero_add,add_zero]
    exact ⟨own.1,own.2.1,by linarith only [own.2.2.1,h0u],by linarith only [lower,side]⟩
  have sp : 0<q.s := lt_of_le_of_ne sn (Ne.symm axis)
  have hs0 := mul_pos h0p sp
  have hc0 := mul_pos h0p cp
  have hs1 := mul_pos h1p sp
  have lowerR : (13/20)*q.c≤q.loU ∨ -(13/20)*q.s≤q.loV := by
    by_cases u : (13/20)*q.c≤q.loU
    · exact Or.inl u
    · right
      apply le_of_not_gt
      intro v
      apply missingR
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [u,v,right.2.1,left.2.2.2,hs1,hc0,sp]
  have top : q.s*(q.loU+q.side)+q.c*(q.loV+q.side)≤1 := by
    rcases upper_bar q h0 h1 cp sp order h0p h0u h1l h1u left right avoid with top | cap
    · exact top
    · rcases lowerR with u | v
      · have first := mul_lt_mul_of_pos_left left.1 cp
        have lower := mul_nonneg cp.le (sub_nonneg.mpr u)
        have last := mul_lt_mul_of_pos_left left.2.2.2 sp
        have upper := mul_nonneg sp.le (sub_nonneg.mpr cap)
        have cross : q.c*q.s≤1/2 := by nlinarith only [q.unit_normal,sq_nonneg (q.c-q.s)]
        nlinarith only [first,lower,last,upper,q.unit_normal,cross]
      · linarith only [cap,v,side,cu]
  have lower0 : 0≤q.loU := by
    apply le_of_not_gt
    intro u
    have v : 0≤q.loV := by
      apply le_of_not_gt
      intro low
      apply missing0
      refine ⟨?_,?_,?_,?_⟩ <;>
        nlinarith only [u,low,left.2.1,left.2.2.2,hs0,hc0]
    have first := mul_lt_mul_of_pos_left right.2.1 sp
    have height := mul_nonneg (sq_nonneg q.s) (sub_nonneg.mpr h1l)
    have last := mul_nonneg cp.le v
    have extra := mul_pos cp (sub_pos.mpr side)
    have coefficient : 0≤(29/20)*q.c+(13/20)*q.s-1 := by
      linarith only [bounds.1,sn]
    have margin := mul_nonneg sn coefficient
    nlinarith only [top,first,height,last,extra,margin,bounds.2.2.2.2]
  have lowerV : -(13/20)*q.s≤q.loV := by
    rcases lowerR with u | v
    · have first := mul_lt_mul_of_pos_left left.1 (sq_pos_of_pos cp)
      have last := mul_lt_mul_of_pos_left left.2.2.2 (mul_pos cp sp)
      have vertexGap : 0<q.c*q.s*(q.loV+q.side)-q.c^2*q.loU := by
        nlinarith only [first,last]
      have wall := mul_le_mul_of_nonneg_left top sn
      have identity : q.s*(q.s*(q.loU+q.side)+q.c*(q.loV+q.side))-
          (q.loU+q.s^2*q.side)=q.c*q.s*(q.loV+q.side)-q.c^2*q.loU := by
        linear_combination q.loU*q.unit_normal
      have excess := mul_pos (sq_pos_of_pos sp) (sub_pos.mpr side)
      nlinarith only [vertexGap,wall,identity,excess,u,bounds.1,sq_nonneg (q.s-1/2)]
    · exact v
  have first := mul_nonneg sn lower0
  have last := mul_nonneg cp.le (sub_nonneg.mpr lowerV)
  have extra := mul_pos (sub_pos.mpr side) (show 0<q.c+q.s by linarith only [cp,sn])
  have cross := mul_nonneg cp.le sn
  nlinarith only [top,first,last,extra,cross,bounds.2.2.2.2]

/-- Reflection of the complete local configuration, exchanging its two
anchor columns. Reindexing the face normals does not change its points. -/
private noncomputable def mirror (q : OpenSquare) : OpenSquare :=
  turnFrame (turnFrame (pullX (q.translated (-67/20) 0)))

private theorem mirror_inside (q : OpenSquare) (x y : ℝ) :
    (mirror q).Inside x y↔q.Inside (13/20-x) y := by
  dsimp only [mirror]
  rw [turnFrame_inside,turnFrame_inside,inside_pullX,inside_translated_iff]
  rw [show (-67/20:ℝ)+(4-x)=13/20-x by ring]
  simp only [zero_add]

/-- The needed r=.65, h0=.74, h1=.65 instance of OTHER-GEOMETRY
Theorem 3, with its complete upper segment and all orientations. -/
theorem local_impossible (q : OpenSquare) (side : 1<q.side)
    (left : q.Inside 0 (37/50)) (right : q.Inside (13/20) (13/20))
    (missing0 : ¬q.Inside 0 0) (missingR : ¬q.Inside (13/20) 0)
    (avoid : ∀ x : ℝ,0≤x → x≤13/20 → ¬q.Inside x 1) : False := by
  obtain ⟨r,cp,range,shape,inside,_⟩ := ClosedFrames.canonical_frame q
  have side' : 1<r.side := by simpa only [shape] using side
  have left' := (inside _ _).mpr left
  have right' := (inside _ _).mpr right
  have missing0' : ¬r.Inside 0 0 := fun own => missing0 ((inside _ _).mp own)
  have missingR' : ¬r.Inside (13/20) 0 := fun own => missingR ((inside _ _).mp own)
  have avoid' : ∀ x : ℝ,0≤x → x≤13/20 → ¬r.Inside x 1 :=
    fun x lo hi own => avoid x lo hi ((inside _ _).mp own)
  by_cases sign : 0≤r.s
  · exact positive_impossible r (37/50) (13/20) side' cp sign
      (by simpa only [abs_of_nonneg sign] using range)
      (by norm_num) (by norm_num) le_rfl (by norm_num)
      left' right' missing0' missingR' avoid'
  · apply positive_impossible (mirror r) (13/20) (37/50) side'
      (by simpa only [mirror,turnFrame,pullX,OpenSquare.translated,neg_neg] using cp)
      (by dsimp only [mirror,turnFrame,pullX,OpenSquare.translated]; linarith only [sign])
      (by
        dsimp only [mirror,turnFrame,pullX,OpenSquare.translated]
        simp only [neg_neg]
        simpa only [abs_of_neg (lt_of_not_ge sign)] using range)
      le_rfl (by norm_num) (by norm_num) (by norm_num)
    · apply (mirror_inside _ _ _).mpr
      norm_num
      exact right'
    · apply (mirror_inside _ _ _).mpr
      norm_num
      exact left'
    · intro own
      apply missingR'
      simpa only [sub_zero] using (mirror_inside _ _ _).mp own
    · intro own
      apply missing0'
      simpa only [sub_self] using (mirror_inside _ _ _).mp own
    · intro x low high own
      exact avoid' (13/20-x) (by linarith only [high]) (by linarith only [low])
        ((mirror_inside _ _ _).mp own)

/-- The upper bar is the strict convex hull of two points in one actual
foreign square. Its endpoints and every interior parameter are retained. -/
theorem foreign_bar_impossible (C W : OpenSquare) (side : 1<C.side)
    (left : C.Inside 0 (37/50)) (right : C.Inside (13/20) (13/20))
    (missing0 : ¬C.Inside 0 0) (missingR : ¬C.Inside (13/20) 0)
    (marker : W.Inside (-43/500) 1) (inner : W.Inside (37/50) 1)
    (apart : ∀ x y,¬(C.Inside x y ∧ W.Inside x y)) : False := by
  apply local_impossible C side left right missing0 missingR
  intro x low high own
  let t := (500/413)*(x+43/500)
  have tn : 0≤t := by dsimp only [t]; linarith only [low]
  have tu : t≤1 := by dsimp only [t]; linarith only [high]
  have foreign : W.Inside x 1 := by
    convert inside_segment W (-43/500) 1 (37/50) 1 t marker inner tn tu using 1
    · dsimp only [t]; ring
    · ring
  exact apart x 1 ⟨own,foreign⟩

end
#print axioms local_impossible
#print axioms foreign_bar_impossible
end N12Compact.Completion.OtherCases.OrdinaryCentralReduction
