import Compact.Completion.C1092.MMMP.TwoFifthsEntranceSoutheast
import Compact.Completion.C1092.TwoFifthsSupport
import Compact.Completion.C1092.TwoFifthsSoutheastScalars
import Compact.Completion.C1092.MMMP.LeftFar

/-! The shared E/W support entrance to the upper-third theorem.
The coupled E floor gives a uniform H_E>-1/80, so the two original
G8 branches share this step. This is a coarser rational consequence of
the same full-square floor, not a transferred bound from either branch. -/
namespace N12Compact.C1092MMMPTwoFifthsEntrance
open S12 S12Pilot ABTransverse C977CornerCubic C1092WholeSupports
open C1092MMMPEndingAxes C1092TwoFifths.Support
set_option Elab.async false

theorem southeast_height (E : OpenSquare) (h : C1092TwoFifths.Southeast E)
    (cap : E.loU+E.side≤E.c-(13/50)*E.s) : -1/80<E.loV+E.side := by
  have b := C1092TwoFifths.Scalars.south_bounds E.c E.s h.cosine h.sine h.small E.unit_normal
  have cu := b.cosineUpper
  have chord := mul_nonneg (show 0≤E.c-12/13 by linarith only [b.cosine])
    (show 0≤1-E.c by linarith only [cu])
  have deficit : 1-E.c≤(13/25)*E.s^2 := by nlinarith only [chord,E.unit_normal]
  have weighted := mul_nonneg (show 0≤1-E.s by linarith only [b.sineUpper])
    (sub_nonneg.mpr deficit)
  have first := mul_nonneg h.sine.le (sub_nonneg.mpr cap)
  have strict := mul_pos (sub_pos.mpr h.side)
    (show 0<E.c+E.s by linarith only [h.cosine,h.sine])
  have low : -13/50*E.s^2+(13/25)*E.s^3<E.c*(E.loV+E.side) := by
    nlinarith only [h.floor,first,strict,weighted,E.unit_normal]
  have polynomial := mul_nonneg (sq_nonneg (E.s-1/3))
    (show 0≤(13/25)*(E.s+1/6) by linarith only [h.sine])
  have numerator : -13/1350<E.c*(E.loV+E.side) := by
    nlinarith only [low,polynomial]
  apply lt_of_not_ge
  intro bad
  have bound := mul_le_mul_of_nonneg_left bad h.cosine.le
  nlinarith only [bound,numerator,b.cosine]

private theorem northwest_cone (E W : OpenSquare) (nx ny : ℝ)
    (unit : nx^2+ny^2=1) (inner : E.Inside 0 (-13/50))
    (forward : E.Inside (13/50) 0)
    (left : W.Inside (-13/50) 0) (north : W.Inside 0 (13/50))
    (sep : upper E nx ny≤lower W nx ny) : nx<0 ∧ 0<ny := by
  have ex := (strict_bounds E _ _ nx ny unit forward).2
  have wx := (strict_bounds W _ _ nx ny unit left).1
  have ey := (strict_bounds E _ _ nx ny unit inner).2
  have wy := (strict_bounds W _ _ nx ny unit north).1
  constructor <;> linarith only [ex,wx,ey,wy,sep]

theorem northwest_axes (E W : OpenSquare) (same : E.side=W.side)
    (cp : 0<E.c) (sp : 0<E.s) (dp : 0<W.c)
    (inner : E.Inside 0 (-13/50)) (forward : E.Inside (13/50) 0)
    (left : W.Inside (-13/50) 0) (north : W.Inside 0 (13/50))
    (apart : ∀ x y,¬(E.Inside x y ∧ W.Inside x y)) :
    E.loV+E.side≤lower W (-E.s) E.c ∨
      upper E (-W.c) (-W.s)≤-(W.loU+W.side) ∨
      upper E (-W.s) W.c≤W.loV := by
  have all := CongruentSAT.faceSeparation_of_disjoint E W same apart
  change pairRadius E W≤|E.c*(centerX W-centerX E)+E.s*(centerY W-centerY E)| ∨
    pairRadius E W≤|-E.s*(centerX W-centerX E)+E.c*(centerY W-centerY E)| ∨
    pairRadius W E≤|W.c*(centerX W-centerX E)+W.s*(centerY W-centerY E)| ∨
    pairRadius W E≤|-W.s*(centerX W-centerX E)+W.c*(centerY W-centerY E)| at all
  have split (nx ny radius : ℝ)
      (identity : supportRadius E nx ny+supportRadius W nx ny=radius)
      (sep : radius≤|nx*(centerX W-centerX E)+ny*(centerY W-centerY E)|) :=
    separated E W nx ny (by rwa [identity])
  have cone := northwest_cone E W
  rcases all with eu|ev|wu|wv
  · rcases split _ _ _ (parallel_radius E W) eu with first|last
    · have no := cone E.c E.s E.unit_normal inner forward left north first
      exact False.elim (by linarith only [no.1,cp])
    · have no := cone (-E.c) (-E.s) (by nlinarith only [E.unit_normal])
        inner forward left north (reverse E W _ _ last)
      exact False.elim (by linarith only [no.2,sp])
  · rcases split _ _ _ (transverse_radius E W) ev with first|last
    · exact Or.inl (by simpa only [(ownV E).2] using first)
    · have no := cone E.s (-E.c) (by nlinarith only [E.unit_normal]) inner forward left north
        (by simpa only [neg_neg] using reverse E W _ _ last)
      exact False.elim (by linarith only [no.2,cp])
  · have radius : supportRadius E W.c W.s+supportRadius W W.c W.s=pairRadius W E := by
      rw [add_comm]; exact parallel_radius W E
    rcases split _ _ _ radius wu with first|last
    · have no := cone W.c W.s W.unit_normal inner forward left north first
      exact False.elim (by linarith only [no.1,dp])
    · right; left
      simpa only [lower_neg,(ownU W).2] using reverse E W _ _ last
  · have radius : supportRadius E (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W E := by
      rw [add_comm]; exact transverse_radius W E
    rcases split _ _ _ radius wv with first|last
    · exact Or.inr (Or.inr (by simpa only [(ownV W).1] using first))
    · have no := cone W.s (-W.c) (by nlinarith only [W.unit_normal]) inner forward left north
        (by simpa only [neg_neg] using reverse E W _ _ last)
      exact False.elim (by linarith only [no.2,dp])

theorem negative_northwest_impossible (E W : OpenSquare)
    (h : C1092TwoFifths.Southeast E) (same : E.side=W.side)
    (wn : Normal W.c (-W.s)) (close : 99/100<W.c) (small : -W.s<7/50)
    (height : -1/80<E.loV+E.side) (wHeight : W.loV+W.side<25/33)
    (origin : W.Inside 0 0) (left : W.Inside (-13/50) 0)
    (north : W.Inside 0 (13/50))
    (apart : ∀ x y,¬(E.Inside x y ∧ W.Inside x y)) : False := by
  have b := C1092TwoFifths.Scalars.south_bounds E.c E.s h.cosine h.sine h.small E.unit_normal
  have wb := normal_bounds wn
  let k := E.c*W.c+E.s*W.s
  let j := E.s*W.c-E.c*W.s
  have cross := mul_nonneg h.sine.le wn.1
  have crossHigh := mul_nonneg (show 0≤8/25-E.s by linarith only [b.sineUpper]) wn.1
  have mainLow := mul_pos (show 0<E.c-47/50 by linarith only [b.cosine])
    (show 0<W.c by linarith only [close])
  have kLow : 22/25<k := by dsimp [k]; nlinarith only [mainLow,crossHigh,close,small]
  have jp : 0<j := by
    have first := mul_pos h.sine (show 0<W.c by linarith only [close])
    have last := mul_nonneg h.cosine.le wn.1
    dsimp [j]; nlinarith only [first,last]
  have jHigh : j<23/50 := by
    have first := mul_nonneg h.sine.le (sub_nonneg.mpr wb.2.1)
    have last := mul_nonneg wn.1 (sub_nonneg.mpr b.cosineUpper)
    dsimp [j]; nlinarith only [first,last,b.sineUpper,small]
  have axes := northwest_axes E W same h.cosine h.sine
    (by linarith only [close]) h.inner h.forward left north apart
  rcases axes with own|opposite|transverse
  · have support := lower_np W (-E.s) E.c (-j) k
      (by dsimp [j]; ring) (by dsimp [k]; ring)
      (by linarith only [jp]) (by linarith only [kLow])
    have upper : 0<W.loU+W.side := by linarith only [origin.2.1]
    have first := mul_pos jp upper
    have length : 1<W.side := by simpa only [←same] using h.side
    have low : W.loV< -8/33 := by linarith only [length,wHeight]
    have last := mul_pos (show 0<k by linarith only [kLow])
      (show 0< -8/33-W.loV by linarith only [low])
    nlinarith only [own,support,first,last,height,kLow]
  · have support := upper_np E (-W.c) (-W.s) (-k) j
      (by dsimp [k]; ring) (by dsimp [j]; ring)
      (by linarith only [kLow]) jp.le
    have first := mul_pos (show 0<k by linarith only [kLow])
      (show 0< -(13/50)*E.s-E.loU by linarith only [h.inner.1])
    have last := mul_pos jp
      (show 0<E.loV+E.side+(13/50)*E.s by linarith only [h.forward.2.2.2])
    have gap := mul_pos h.sine (show 0<k-j by linarith only [kLow,jHigh])
    nlinarith only [opposite,support,first,last,gap,origin.2.1]
  · have no := northwest_cone E W (-W.s) W.c
      (by nlinarith only [W.unit_normal]) h.inner h.forward left north
      (by simpa only [(ownV W).1] using transverse)
    linarith only [no.1,wn.1]

theorem positive_northwest_height (E W : OpenSquare)
    (h : C1092TwoFifths.Southeast E) (same : E.side=W.side)
    (wn : Normal W.c W.s) (height : -1/80<E.loV+E.side)
    (origin : W.Inside 0 0) (left : W.Inside (-13/50) 0)
    (north : W.Inside 0 (13/50))
    (apart : ∀ x y,¬(E.Inside x y ∧ W.Inside x y)) : 24/25<W.loV+W.side := by
  have wb := normal_bounds wn
  have dp : 0<W.c := by linarith only [wb.1]
  have eo : E.s≤E.c := by linarith only [h.small,h.sine]
  let k := W.c*E.c+W.s*E.s
  let j := W.s*E.c-W.c*E.s
  have kp : 0<k := by
    have first := mul_pos dp h.cosine
    have last := mul_nonneg wn.1 h.sine.le
    dsimp [k]; linarith only [first,last]
  have unit : k^2+j^2=1 := by
    calc
      _ = (W.c^2+W.s^2)*(E.c^2+E.s^2) := by dsimp [k,j]; ring
      _ = 1 := by rw [W.unit_normal,E.unit_normal]; norm_num
  have minus : 0≤k-j := by
    have a := mul_nonneg (sub_nonneg.mpr wn.2.1) h.cosine.le
    have b := mul_nonneg (show 0≤W.c+W.s by linarith only [dp,wn.1]) h.sine.le
    dsimp [k,j]; nlinarith only [a,b]
  have plus : 0≤k+j := by
    have a := mul_nonneg (sub_nonneg.mpr eo) dp.le
    have b := mul_nonneg wn.1 (show 0≤E.c+E.s by linarith only [h.cosine,h.sine])
    dsimp [k,j]; nlinarith only [a,b]
  have square := mul_nonneg minus plus
  have kLow : 7/10<k := by nlinarith only [square,unit,kp,sq_nonneg (k-7/10)]
  have kHigh : k≤1 := by nlinarith only [unit,sq_nonneg j,sq_nonneg (k-1)]
  have length : 1<W.side := by simpa only [←same] using h.side
  have uLow : E.loU<0 := by linarith only [h.inner.1,h.sine]
  have uHigh : 0<E.loU+E.side := by linarith only [h.forward.2.1,h.cosine]
  have axes := northwest_axes E W same h.cosine h.sine dp h.inner h.forward left north apart
  rcases axes with own|opposite|transverse
  · have bound : lower W (-E.s) E.c≤k*W.loV := by
      by_cases sign : 0≤j
      · have support := lower_nn W (-E.s) E.c j k
          (by dsimp [j]; ring) (by dsimp [k]; ring) sign kp.le
        have first := mul_nonpos_of_nonneg_of_nonpos sign
          (show W.loU≤0 by linarith only [origin.1])
        linarith only [support,first]
      · have sign' : j≤0 := (lt_of_not_ge sign).le
        have support := lower_np W (-E.s) E.c j k
          (by dsimp [j]; ring) (by dsimp [k]; ring) sign' kp.le
        have first := mul_nonpos_of_nonpos_of_nonneg sign'
          (show 0≤W.loU+W.side by linarith only [origin.2.1])
        linarith only [support,first]
    apply lt_of_not_ge
    intro low
    have product := mul_pos kp
      (show 0< -1/25-W.loV by linarith only [low,length])
    nlinarith only [height,own,bound,product,kLow]
  · have no := northwest_cone E W (-W.c) (-W.s)
      (by nlinarith only [W.unit_normal]) h.inner h.forward left north
      (by simpa only [lower_neg,(ownU W).2] using opposite)
    exact False.elim (by linarith only [no.2,wn.1])
  · have bound : k*(E.loV+E.side)≤upper E (-W.s) W.c := by
      by_cases sign : 0≤j
      · have support := upper_np E (-W.s) W.c (-j) k
          (by dsimp [j]; ring) (by dsimp [k]; ring) (by linarith only [sign]) kp.le
        have first := mul_nonneg sign (show 0≤-E.loU by linarith only [uLow])
        linarith only [support,first]
      · have sign' : 0≤-j := by linarith only [lt_of_not_ge sign]
        have support := upper_pos_pos E (-W.s) W.c (-j) k
          (by dsimp [j]; ring) (by dsimp [k]; ring) sign' kp.le
        have first := mul_nonneg sign' uHigh.le
        linarith only [support,first]
    have strict := mul_pos kp (show 0<E.loV+E.side+1/80 by linarith only [height])
    nlinarith only [strict,kHigh,bound,transverse,length]

theorem positive_northwest_faces (W : OpenSquare) (side : 1<W.side)
    (wn : Normal W.c W.s) (origin : W.Inside 0 0)
    (diagonal : W.Inside (-1/2) (1/2))
    (missingSW : ¬W.Inside (-7/20) (-7/20))
    (missingNE : ¬W.Inside (7/20) (7/20))
    (missingLeft : ¬W.Inside (-1) (39/100)) : 8*W.s<7*W.c := by
  have wb := normal_bounds wn
  have cp : 0<W.c := by linarith only [wb.1]
  have upperU : W.loU+W.side≤(7/20)*(W.c+W.s) := by
    apply le_of_not_gt
    intro high
    apply missingNE
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [origin.1,origin.2.2.1,diagonal.2.2.2,high,cp,wn.1,wn.2.1]
  have lowerV : -(7/20)*(W.c-W.s)≤W.loV := by
    apply le_of_not_gt
    intro low
    apply missingSW
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [upperU,side,wb.2.2.2.2.2,origin.2.1,origin.2.2.2,
        low,cp,wn.1,wn.2.1]
  have short := (short_projections W (37/50) (13/20) (by norm_num)).2.1
  have lowerU : -W.c+(39/100)*W.s≤W.loU := by
    apply le_of_not_gt
    intro low
    apply missingLeft
    refine ⟨?_,?_,?_,?_⟩ <;>
      linarith only [origin.2.1,origin.2.2.1,lowerV,side,short,low,cp,wn.1,wn.2.1]
  have width : W.side≤(27/20)*W.c-(1/25)*W.s := by linarith only [lowerU,upperU]
  apply lt_of_not_ge
  intro high
  have product := mul_nonneg (show 0≤8*W.s-7*W.c by linarith only [high])
    (show 0≤8*W.s+7*W.c by linarith only [cp,wn.1])
  have close : 200/263<W.c := by linarith only [width,side,high]
  have gap := mul_pos (sub_pos.mpr close)
    (show 0<W.c+200/263 by linarith only [cp])
  nlinarith only [product,gap,W.unit_normal]

theorem positive_northwest_left_face (W : OpenSquare) (wn : Normal W.c W.s)
    (slope : 8*W.s<7*W.c) (height : 24/25<W.loV+W.side)
    (origin : W.Inside 0 0) (missing : ¬W.Inside (-1) (2/5)) :
    W.side-W.c+(2/5)*W.s≤W.loU+W.side := by
  have wb := normal_bounds wn
  have cp : 0<W.c := by linarith only [wb.1]
  have product := mul_nonneg (show 0≤7*W.c-8*W.s by linarith only [slope])
    (show 0≤(307/25)*W.c+(28/25)*W.s by linarith only [cp,wn.1])
  have short : W.s+(2/5)*W.c<24/25 := by
    nlinarith only [product,W.unit_normal,sq_nonneg (W.s+(2/5)*W.c-24/25)]
  apply le_of_not_gt
  intro low
  apply missing
  refine ⟨?_,?_,?_,?_⟩ <;>
    linarith only [low,height,short,origin.2.1,origin.2.2.1,cp,wn.1,wn.2.1]

#print axioms southeast_height
#print axioms positive_northwest_height
end N12Compact.C1092MMMPTwoFifthsEntrance
