import Compact.Completion.C1092.MMMP.EndingAxes
import Compact.Completion.C1092.MMMP.FinalScalars39
import Compact.Completion.C1092.MMMMFirstPair
import Compact.Completion.CommonCases.CanonicalProjection
import Compact.Geometry.ClosedFrames

/-! The complete final MMMP pair contradiction, conditional only on the
same actual NE square's full face table. It uses the universal left wall
endpoint2.39 and only the actual NW center, left halfpoint and diagonal.
This local profile theorem is not itself the original BranchEnding1. -/
namespace N12Compact.C1092MMMPEnding
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports C1092ShortChordTable
open C1092MMMPEndingAxes
set_option Elab.async false

def Profile (N : OpenSquare) : Prop :=
  (2/5)*N.s≤N.loU ∧ (14/25)*N.c-N.s≤N.loV ∧
    N.loU+N.side≤N.c+N.s ∧ N.loV+N.side≤N.c

private theorem cosine_cap {b t : ℝ} (bn : Normal b t) (steep : 252/373≤t) :
    b≤275/373 := by
  have t2 := mul_nonneg (sub_nonneg.mpr steep)
    (show 0≤t+252/373 by linarith only [bn.1])
  nlinarith only [bn.2.2,t2,sq_nonneg (b-275/373)]

private theorem negative (W N : OpenSquare) (side : 1<W.side) (same : W.side=N.side)
    (dn : Normal W.c (-W.s)) (bn : Normal N.c N.s) (steep : 252/373≤N.s)
    (faces : Profile N)
    (origin : W.Inside 0 0) (left : W.Inside (-1/2) 0)
    (diagonal : W.Inside (-1/2) (1/2)) (wm : W.Inside (-7/20) (7/20))
    (missingSW : ¬W.Inside (-7/20) (-7/20))
    (nm : N.Inside (7/20) (7/20))
    (h1 : N.Inside (13/50) 1) (h2 : N.Inside (2/5) 1)
    (apart : ∀ x y, ¬(W.Inside x y ∧ N.Inside x y)) : False := by
  let C := clockwise W
  let B := clockwise N
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have bp : 0<N.c := by linarith only [bb.1]
  have f : PositiveFaces B.c B.s B.loU B.loV B.side := by
    dsimp [PositiveFaces,B,clockwise]
    rcases faces with ⟨a,b,c,d⟩
    refine ⟨?_,?_,?_,?_⟩ <;> linarith only [a,b,c,d,bn.1,bp]
  have out0 : ¬B.Inside (-1) 0 := by
    intro own
    dsimp [PositiveFaces] at f
    dsimp [OpenSquare.Inside,InBands] at own
    linarith only [f.1,own.1]
  have out1 : ¬B.Inside (-1) 1 := by
    intro own
    dsimp [PositiveFaces] at f
    dsimp [OpenSquare.Inside,InBands] at own
    linarith only [f.2.2.2,own.2.2.2]
  have out2 : ¬B.Inside (-39/100) 0 := by
    intro own
    dsimp [PositiveFaces] at f
    dsimp [OpenSquare.Inside,InBands] at own
    linarith only [f.2.2.1,own.2.2.1]
  have out3 : ¬B.Inside (-39/100) 1 := by
    intro own
    dsimp [PositiveFaces] at f
    dsimp [OpenSquare.Inside,InBands] at own
    linarith only [f.2.1,own.2.1]
  have result := C1092MMMMFirstPair.result C B side same dn bp
    (by simpa only [B,clockwise,abs_of_nonneg bn.1] using bn.2.1)
    (by simpa only [C,inside_clockwise,neg_zero] using origin)
    (by apply (inside_clockwise _ _ _).mpr; convert left using 1 <;> norm_num)
    (by apply (inside_clockwise _ _ _).mpr; convert wm using 1 <;> norm_num)
    (by
      intro own
      apply missingSW
      have h := (inside_clockwise _ _ _).mp own
      convert h using 1 <;> norm_num)
    (by apply (inside_clockwise _ _ _).mpr; convert nm using 1 <;> norm_num)
    (by apply (inside_clockwise _ _ _).mpr; convert h1 using 1 <;> norm_num)
    (by apply (inside_clockwise _ _ _).mpr; convert h2 using 1 <;> norm_num)
    out0 out1 out2 out3
    (by
      intro x y own
      exact apart y (-x)
        ⟨(inside_clockwise _ _ _).mp own.1,(inside_clockwise _ _ _).mp own.2⟩)
  let d := W.c
  let r := -W.s
  let b := N.c
  let t := N.s
  let A := W.loU+W.side
  let H := W.loV+W.side
  let alpha := b*d-t*r
  let k := b*r+t*d
  let h := d+r
  have ap : 0≤alpha := by
    have first := mul_nonneg (sub_nonneg.mpr bn.2.1) (by linarith only [db.1] : 0≤W.c)
    have last := mul_nonneg bn.1 (sub_nonneg.mpr dn.2.1)
    dsimp [alpha,b,t,d,r]
    nlinarith only [first,last]
  have Ap : 0<A := by dsimp [A]; linarith only [origin.2.1]
  have Hp : 0<H := by dsimp [H]; linarith only [origin.2.2.2]
  have support : alpha*A+k*H≤b+t-W.side := by
    have raw := result.support
    dsimp [C,B,clockwise] at raw
    dsimp [alpha,A,k,H,b,t,d,r]
    nlinarith only [raw]
  have endpoint := CommonCases.CanonicalProjection.after b t (275/373) (252/373) 18 7
    bn.2.2 (by norm_num)
    (by dsimp [b,t]; linarith only [cosine_cap bn steep,steep]) (by norm_num) (by norm_num)
  norm_num at endpoint
  have kBound : t*h≤k := by
    have product := mul_nonneg dn.1 (sub_nonneg.mpr bn.2.1)
    dsimp [t,h,k,b,d,r]
    nlinarith only [product]
  have first := mul_nonneg ap Ap.le
  have last := mul_le_mul_of_nonneg_right kBound Hp.le
  have tp : 0<t := by dsimp [t]; linarith only [steep]
  have small : h*H<11/18 := by
    apply (mul_lt_mul_left tp).mp
    nlinarith only [support,first,last,side,endpoint]
  have lowerFace : -(7/20)*h≤W.loV := by
    apply le_of_not_gt
    intro low
    apply missingSW
    refine ⟨?_,?_,?_,?_⟩ <;>
      dsimp [h,d,r] at low ⊢ <;>
      linarith only [low,origin.2.1,origin.2.2.2,diagonal.1,db.1,dn.1,dn.2.1]
  have hp : 0<h := by dsimp [h,d,r]; linarith only [db.1,dn.1]
  have hlo : 1≤h := db.2.2.2.2.1
  have hhi : h≤10/7 := db.2.2.2.2.2
  have chord := mul_nonneg (sub_nonneg.mpr hlo)
    (show 0≤13/20-(7/20)*h by linarith only [hhi])
  have strict := mul_pos hp (show 0<H-(1-(7/20)*h) by
    dsimp [H]; linarith only [lowerFace,side])
  nlinarith only [small,chord,strict]

private theorem positive (W N : OpenSquare) (side : 1<W.side) (same : W.side=N.side)
    (dn : Normal W.c W.s) (bn : Normal N.c N.s) (steep : 252/373≤N.s)
    (faces : Profile N)
    (origin : W.Inside 0 0) (left : W.Inside (-1/2) 0)
    (diagonal : W.Inside (-1/2) (1/2)) (wm : W.Inside (-7/20) (7/20))
    (missingSW : ¬W.Inside (-7/20) (-7/20)) (missingLeft : ¬W.Inside (-1) (39/100))
    (nm : N.Inside (7/20) (7/20))
    (apart : ∀ x y, ¬(W.Inside x y ∧ N.Inside x y)) : False := by
  classical
  have db := normal_bounds dn
  have bb := normal_bounds bn
  have dp : 0<W.c := by linarith only [db.1]
  have bp : 0<N.c := by linarith only [bb.1]
  have missingNE : ¬W.Inside (7/20) (7/20) := fun own => apart _ _ ⟨own,nm⟩
  let C := clockwise W
  have zero : C.Inside 0 0 := by simpa only [C,inside_clockwise,neg_zero] using origin
  have mark : C.Inside (-7/20) (-7/20) := by
    apply (inside_clockwise _ _ _).mpr
    convert wm using 1 <;> norm_num
  have diag : C.Inside (-1/2) (-1/2) := by
    apply (inside_clockwise _ _ _).mpr
    convert diagonal using 1 <;> norm_num
  have omitM : ¬C.Inside (-7/20) (7/20) := by
    intro own
    apply missingNE
    have h := (inside_clockwise _ _ _).mp own
    convert h using 1 <;> norm_num
  have omitG : ¬C.Inside (7/20) (-7/20) := by
    intro own
    apply missingSW
    have h := (inside_clockwise _ _ _).mp own
    convert h using 1 <;> norm_num
  have omitF : ¬C.Inside (-39/100) (-1) := by
    intro own
    apply missingLeft
    have h := (inside_clockwise _ _ _).mp own
    convert h using 1 <;> norm_num
  have vCap : C.loV+C.side≤(7/20)*(W.c+W.s) := by
    apply le_of_not_gt
    intro upper
    apply omitM
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [C,clockwise] at upper ⊢ <;>
      linarith only [upper,diag.1,zero.2.1,mark.2.2.1,dp,dn.1,dn.2.1]
  have uCap : C.loU+C.side≤(7/20)*(W.c-W.s) := by
    apply le_of_not_gt
    intro upper
    have lowV : C.loV< -(7/20)*(W.c+W.s) := by
      dsimp [C,clockwise] at vCap ⊢
      linarith only [vCap,side,db.2.2.2.2.2]
    apply omitG
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [C,clockwise] at upper lowV ⊢ <;>
      linarith only [upper,lowV,zero.1,mark.2.2.2,dp,dn.1,dn.2.1]
  have vFloor : C.side+(39/100)*W.s-W.c≤C.loV+C.side := by
    have short := (short_projections W (37/50) (13/20) (by norm_num)).2.1
    have lowU : C.loU< -(39/100)*W.c-W.s := by
      dsimp [C,clockwise] at uCap ⊢
      linarith only [uCap,side,short]
    apply le_of_not_gt
    intro cap
    apply omitF
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [C,clockwise] at cap lowU ⊢ <;>
      linarith only [cap,lowU,mark.2.1,mark.2.2.2,dp,dn.1,dn.2.1]
  have shallow : 8*W.s<7*W.c := by
    apply lt_of_not_ge
    intro high
    have square := mul_nonneg (show 0≤8*W.s-7*W.c by linarith only [high])
      (show 0≤8*W.s+7*W.c by linarith only [dp,dn.1])
    have width : W.side≤(27/20)*W.c-(1/25)*W.s := by
      dsimp [C,clockwise] at vCap vFloor
      linarith only [vCap,vFloor]
    have cosine : 200/263<W.c := by linarith only [width,side,high]
    have gap := mul_pos (sub_pos.mpr cosine)
      (show 0<W.c+200/263 by linarith only [dp])
    nlinarith only [square,gap,W.unit_normal]
  let d := W.c
  let r := W.s
  let b := N.c
  let t := N.s
  let A := W.loU+W.side
  let H := W.loV+W.side
  let alpha := b*d+t*r
  let beta := t*d-b*r
  have ap : 0<alpha := by
    have first := mul_pos bp dp
    have last := mul_nonneg bn.1 dn.1
    dsimp [alpha,b,t,d,r]
    linarith only [first,last]
  have betap : 0<beta := by
    have first := mul_pos dp (show 0<N.s-(7/8)*N.c by
      linarith only [cosine_cap bn steep,steep])
    have last := mul_pos bp (show 0<(7/8)*W.c-W.s by linarith only [shallow])
    dsimp [beta,t,b,d,r]
    nlinarith only [first,last]
  have relative : alpha^2+beta^2=1 := by
    calc
      _ = (b^2+t^2)*(d^2+r^2) := by dsimp [alpha,beta]; ring
      _ = 1 := by rw [bn.2.2,dn.2.2]; norm_num
  have alphaOne : alpha≤1 := by nlinarith only [relative,sq_nonneg beta,sq_nonneg (alpha-1)]
  have relativeSum : 1≤alpha+beta := by
    nlinarith only [relative,mul_pos ap betap,ap,betap]
  have Nheight : 0<N.loV+N.side := by
    dsimp [Profile] at faces
    rw [←same]
    linarith only [faces.2.1,side,bn.2.1,bb.2.1]
  have Nlow : N.loU<1/2 := by
    dsimp [Profile] at faces
    rw [←same] at faces
    linarith only [faces.2.2.1,side,bb.2.2.2.2.2]
  have lowerFormula := lower_pn N d r alpha (-beta)
    (by dsimp [d,r,alpha,b,t]; ring) (by dsimp [d,r,beta,b,t]; ring)
    ap.le (by linarith only [betap])
  have upperFormula := upper_nn W b t alpha beta
    (by dsimp [d,r,alpha,b,t]; ring) (by dsimp [d,r,beta,b,t]; ring) ap.le betap.le
  have lowOwn : lower N d r<1/2 := by
    have weighted : alpha*N.loU<1/2 := by
      by_cases sign : 0≤N.loU
      · have bound := mul_le_mul_of_nonneg_right alphaOne sign
        linarith only [bound,Nlow]
      · have bound := mul_nonpos_of_nonneg_of_nonpos ap.le (le_of_not_ge sign)
        linarith only [bound]
    have last := mul_pos betap Nheight
    nlinarith only [lowerFormula,weighted,last]
  have Hp : 1/2<H := by
    dsimp [H]
    linarith only [diagonal.2.2.2,db.2.2.2.2.1]
  have axes := C1092MMMPEndingAxes.alternatives W N same dp dn.1 dn.2.1 bp bn.1 bn.2.1
    origin wm nm apart
  have sLowU : W.loU<d*(-7/20)+r*(-7/20) := by
    apply lt_of_not_ge
    intro face
    have Ap : 1/2<A := by
      dsimp [A]
      linarith only [face,side,db.2.2.2.2.2]
    rcases axes with own | neighbor
    · change A≤lower N d r at own
      linarith only [own,Ap,lowOwn]
    · have first := mul_pos ap (show 0<A-1/2 by linarith only [Ap])
      have last := mul_pos betap (show 0<H-1/2 by linarith only [Hp])
      dsimp [A,H] at upperFormula
      nlinarith only [neighbor,upperFormula,first,last,relativeSum,Nlow]
  have hFace : W.side-(7/20)*d+(7/20)*r≤H := by
    apply le_of_not_gt
    intro face
    apply missingSW
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [A,H,d,r] at sLowU face ⊢ <;>
      linarith only [sLowU,face,origin.2.1,origin.2.2.2,dn.1,dn.2.1]
  have aFace : W.side-d+(39/100)*r≤A := by
    have highV : r+(39/100)*d<W.loV+W.side := by
      have short := (short_projections W (37/50) (13/20) (by norm_num)).2.1
      dsimp [H,d,r] at hFace ⊢
      linarith only [hFace,side,short]
    apply le_of_not_gt
    intro face
    apply missingLeft
    refine ⟨?_,?_,?_,?_⟩ <;> dsimp [A,d,r] at face highV ⊢ <;>
      linarith only [face,highV,origin.1,origin.2.1,origin.2.2.1,dp,dn.1,dn.2.1]
  have coef : 0<1+alpha+beta := by linarith only [ap,betap]
  have strict := mul_pos (sub_pos.mpr side) coef
  rcases axes with own | neighbor
  · have upperU : N.loU≤b+t-W.side := by
      dsimp [Profile,b,t] at faces ⊢
      rw [←same] at faces
      linarith only [faces.2.2.1]
    have lowerV : W.side+(2/5)*b-t≤N.loV+N.side := by
      dsimp [Profile,b,t] at faces ⊢
      rw [←same]
      linarith only [faces.2.1,bp]
    have first := mul_le_mul_of_nonneg_left upperU ap.le
    have last := mul_le_mul_of_nonneg_left lowerV betap.le
    have margin := C1092MMMPFinalScalars39.own_positive dn bn
      (by linarith only [steep])
    dsimp [C1092MMMPFinalScalars39.ownMargin] at margin
    change A≤lower N d r at own
    dsimp [alpha,beta,d,r,b,t] at first last strict lowerFormula own aFace margin
    nlinarith only [own,lowerFormula,first,last,aFace,strict,margin]
  · have upperU : N.loU≤b+t-W.side := by
      dsimp [Profile,b,t] at faces ⊢
      rw [←same] at faces
      linarith only [faces.2.2.1]
    have first := mul_le_mul_of_nonneg_left aFace ap.le
    have last := mul_le_mul_of_nonneg_left hFace betap.le
    have margin := C1092MMMPFinalScalars39.neighbor_positive dn bn steep
    dsimp [C1092MMMPFinalScalars39.neighborMargin] at margin
    dsimp [alpha,beta,d,r,b,t] at first last strict upperFormula upperU margin
    nlinarith only [neighbor,upperFormula,first,last,upperU,strict,margin]

theorem impossible (W N : OpenSquare) (side : 1<W.side) (same : W.side=N.side)
    (bn : Normal N.c N.s) (steep : 252/373≤N.s) (faces : Profile N)
    (origin : W.Inside 0 0) (left : W.Inside (-1/2) 0)
    (diagonal : W.Inside (-1/2) (1/2)) (wm : W.Inside (-7/20) (7/20))
    (missingSW : ¬W.Inside (-7/20) (-7/20)) (missingLeft : ¬W.Inside (-1) (39/100))
    (nm : N.Inside (7/20) (7/20))
    (h1 : N.Inside (13/50) 1) (h2 : N.Inside (2/5) 1)
    (apart : ∀ x y, ¬(W.Inside x y ∧ N.Inside x y)) : False := by
  classical
  obtain ⟨C,cp,canonical,shape,inside,_⟩ := ClosedFrames.canonical_frame W
  have ca : 1<C.side := by simpa only [shape] using side
  have cs : C.side=N.side := shape.trans same
  have co := (inside _ _).mpr origin
  have cl := (inside _ _).mpr left
  have cd := (inside _ _).mpr diagonal
  have cm := (inside _ _).mpr wm
  have cSW : ¬C.Inside (-7/20) (-7/20) := fun own => missingSW ((inside _ _).mp own)
  have cLeft : ¬C.Inside (-1) (39/100) := fun own => missingLeft ((inside _ _).mp own)
  have disjoint : ∀ x y, ¬(C.Inside x y ∧ N.Inside x y) :=
    fun x y own => apart x y ⟨(inside x y).mp own.1,own.2⟩
  by_cases sign : 0≤C.s
  · exact positive C N ca cs
      ⟨sign,by simpa only [abs_of_nonneg sign] using canonical,C.unit_normal⟩ bn steep faces
      co cl cd cm cSW cLeft nm disjoint
  · exact negative C N ca cs
      ⟨by linarith only [sign],by simpa only [abs_of_neg (lt_of_not_ge sign)] using canonical,
        by nlinarith only [C.unit_normal]⟩ bn steep faces co cl cd cm cSW nm h1 h2 disjoint

#print axioms impossible
end N12Compact.C1092MMMPEnding
