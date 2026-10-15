import Compact.Geometry.C84MergedBottom
import Compact.Geometry.C84PairMargins
import Compact.Geometry.ABTransverse

/-! A two-square continuous contradiction for the original merged owners
of case84. The missing G5 premise is essential: the G-budget supplies it
after choosing G6. Both axes of each physical square are exhausted. -/
namespace N12Compact.C84MergedPair
open S12 S12Pilot FourSquareAnchors ThreeSquare C977ChainBridge ABTransverse
open C977CornerCubic
set_option Elab.async false

private theorem canonical_impossible (B W : OpenSquare)
    (ha : 1<B.side) (same : B.side=W.side)
    (bc : 0<B.c) (bs : 0<B.s) (canonicalB : B.s≤B.c)
    (wc : 0<W.c) (canonicalW : |W.s|≤W.c)
    (bottom : B.Inside 2 (457/500))
    (southeast : B.Inside (47/20) (33/20))
    (right : B.Inside (113/50) 2)
    (southwest : W.Inside (33/20) (33/20))
    (northwest : W.Inside (33/20) (47/20))
    (inner : W.Inside (87/50) 2)
    (missingSW : ¬B.Inside (33/20) (33/20))
    (missingG5 : ¬B.Inside (113/50) 1)
    (apart : ∀ x y, ¬(B.Inside x y ∧ W.Inside x y)) : False := by
  have bn : Normal B.c B.s := ⟨bs.le,canonicalB,B.unit_normal⟩
  have wb := abs_le.mp canonicalW
  have lowerV : B.c-(113/50)*B.s≤B.loV := by
    apply le_of_not_gt
    intro hv
    apply missingG5
    refine ⟨?_,?_,by linarith only [hv],?_⟩
    · linarith only [bottom.1,bc,bs]
    · linarith only [southeast.2.1,bc,bs]
    · linarith only [right.2.2.2,bc]
  have tilted : (43/500)*B.c<(13/50)*B.s := by
    linarith only [bottom.2.2.1,lowerV]
  have steep : (3/10 : ℝ)<B.s := by
    apply lt_of_not_ge
    intro small
    have product := mul_nonneg (sub_nonneg.mpr small)
      (show 0≤(3/10 : ℝ)+B.s by linarith only [bs])
    have cosine : (19/20 : ℝ)≤B.c := by
      nlinarith only [product,B.unit_normal,bc]
    linarith only [tilted,small,cosine]
  have gap := C84PairMargins.parallel bn
  have lowerU : (33/20)*(B.c+B.s)≤B.loU := by
    apply le_of_not_gt
    intro hu
    apply missingSW
    refine ⟨by linarith only [hu],?_,?_,?_⟩
    · linarith only [southeast.2.1,bc]
    · linarith only [bottom.2.2.1,bc,bs]
    · linarith only [lowerV,ha,gap]
  let alpha := W.c*B.c+W.s*B.s
  let beta := W.s*B.c-W.c*B.s
  have alphaNonnegative : 0≤alpha := by
    have one := mul_nonneg (sub_nonneg.mpr canonicalB) wc.le
    have two := mul_nonneg bs.le (show 0≤W.c+W.s by linarith only [wb.1])
    dsimp [alpha]
    nlinarith only [one,two]
  have alphaUnit : alpha^2+beta^2=1 := by
    calc
      _ = (W.c^2+W.s^2)*(B.c^2+B.s^2) := by dsimp [alpha,beta]; ring
      _ = 1 := by rw [W.unit_normal,B.unit_normal]; norm_num
  have noBU (sep : upper B B.c B.s≤lower W B.c B.s ∨
      upper W B.c B.s≤lower B B.c B.s) : False := by
    have se := strict_bounds B _ _ B.c B.s B.unit_normal southeast
    have sw := strict_bounds W _ _ B.c B.s B.unit_normal southwest
    have low := strict_bounds B _ _ B.c B.s B.unit_normal bottom
    have nw := strict_bounds W _ _ B.c B.s B.unit_normal northwest
    rcases sep with sep | sep
    · nlinarith only [sep,se.2,sw.1,bc]
    · nlinarith only [sep,low.1,nw.2,tilted,bc]
  have noBV (sep : upper B (-B.s) B.c≤lower W (-B.s) B.c ∨
      upper W (-B.s) B.c≤lower B (-B.s) B.c) : False := by
    have unit : (-B.s)^2+B.c^2=1 := by nlinarith only [B.unit_normal]
    have sw := strict_bounds W _ _ (-B.s) B.c unit southwest
    have nw := strict_bounds W _ _ (-B.s) B.c unit northwest
    have se := strict_bounds B _ _ (-B.s) B.c unit southeast
    rcases sep with sep | sep
    · rw [(ownV B).2] at sep
      nlinarith only [sep,sw.1,lowerV,ha,gap]
    · nlinarith only [sep,nw.2,se.1,bc,bs]
  have noWU (sep : upper B W.c W.s≤lower W W.c W.s ∨
      upper W W.c W.s≤lower B W.c W.s) : False := by
    have se := strict_bounds B _ _ W.c W.s W.unit_normal southeast
    have sw := strict_bounds W _ _ W.c W.s W.unit_normal southwest
    rcases sep with sep | sep
    · nlinarith only [sep,se.2,sw.1,wc]
    by_cases order : 0≤beta
    · have ws : 0≤W.s := by
        dsimp [beta] at order
        nlinarith only [order,bc,wc,bs]
      have cosine : B.c≤1 := by nlinarith only [B.unit_normal,sq_nonneg B.s,bc]
      have product := mul_nonneg ws (sub_nonneg.mpr cosine)
      have ordered := mul_le_mul_of_nonneg_right steep.le wc.le
      have slope : (3/10)*W.c≤W.s := by
        dsimp [beta] at order
        nlinarith only [order,ordered,product]
      have low := strict_bounds B _ _ W.c W.s W.unit_normal bottom
      have high := strict_bounds W _ _ W.c W.s W.unit_normal northwest
      nlinarith only [sep,low.1,high.2,slope,wc]
    have negative : beta≤0 := (lt_of_not_ge order).le
    have support : lower B W.c W.s=alpha*B.loU+beta*(B.loV+B.side) := by
      dsimp [lower,supportRadius,centerX,centerY]
      rw [abs_of_nonneg (show 0≤W.c*B.c+W.s*B.s from alphaNonnegative),
        abs_of_nonpos (show -W.c*B.s+W.s*B.c≤0 by dsimp [beta] at negative; linarith only [negative])]
      dsimp [alpha,beta]
      ring
    have first := mul_le_mul_of_nonneg_left bottom.1.le alphaNonnegative
    have second := mul_le_mul_of_nonpos_left
      (show 1+B.c-(113/50)*B.s≤B.loV+B.side by linarith only [lowerV,ha]) negative
    let X := 2+(13/50)*B.s^2-(43/500)*B.c*B.s-B.s
    let Y := 1-(43/500)*B.s^2-(13/50)*B.c*B.s+B.c
    have identity : alpha*(2*B.c+(457/500)*B.s)+
        beta*(1+B.c-(113/50)*B.s)=W.c*X+W.s*Y := by
      dsimp [alpha,beta,X,Y]
      nlinarith only [congrArg (fun z : ℝ => W.c*z) B.unit_normal,
        congrArg (fun z : ℝ => W.s*z) B.unit_normal]
    have bound : lower B W.c W.s≤W.c*X+W.s*Y := by
      rw [support]
      linarith only [first,second,identity]
    have scalar := C84PairMargins.margins bn steep.le
    let A := C84PairMargins.A B.c B.s
    let D := C84PairMargins.D B.c B.s
    have x : X=A+87/50 := by dsimp [X,A,C84PairMargins.A]; ring
    have y : Y=D+2 := by dsimp [Y,D,C84PairMargins.D]; ring
    rw [x,y] at bound
    have innerBound := (strict_bounds W _ _ W.c W.s W.unit_normal inner).2
    by_cases ws : 0≤W.s
    · have one := mul_neg_of_pos_of_neg wc scalar.1
      have two := mul_nonpos_of_nonneg_of_nonpos ws scalar.2.1
      change W.c*A<0 at one
      change W.s*D≤0 at two
      nlinarith only [sep,bound,innerBound,one,two,x,y]
    have rnonnegative : 0≤-W.s := (neg_nonneg.mpr (le_of_not_ge ws))
    by_cases low : 35*(-W.s)≤9*W.c
    · have one := mul_neg_of_pos_of_neg wc scalar.2.2.1
      have two := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr low) scalar.2.1
      change W.c*(35*A-9*D)<0 at one
      change (9*W.c-35*(-W.s))*D≤0 at two
      nlinarith only [sep,bound,innerBound,one,two,x,y]
    have high : 0<35*(-W.s)-9*W.c := by linarith only [lt_of_not_ge low]
    have one := mul_nonpos_of_nonneg_of_nonpos
      (show 0≤W.c+W.s by linarith only [wb.1]) scalar.2.2.1.le
    have two := mul_neg_of_pos_of_neg high scalar.2.2.2
    change (W.c+W.s)*(35*A-9*D)≤0 at one
    change (35*(-W.s)-9*W.c)*(A-D-13/50)<0 at two
    nlinarith only [sep,bound,sw.2,one,two,x,y]
  have noWV (sep : upper B (-W.s) W.c≤lower W (-W.s) W.c ∨
      upper W (-W.s) W.c≤lower B (-W.s) W.c) : False := by
    have unit : (-W.s)^2+W.c^2=1 := by nlinarith only [W.unit_normal]
    have sw := (strict_bounds W _ _ (-W.s) W.c unit southwest).1
    have nw := (strict_bounds W _ _ (-W.s) W.c unit northwest).2
    have low := (strict_bounds B _ _ (-W.s) W.c unit bottom).1
    rcases sep with sep | sep
    swap
    · nlinarith only [sep,nw,low,wb.1,wc]
    by_cases order : beta≤0
    · have support : upper B (-W.s) W.c=
          -beta*(B.loU+B.side)+alpha*(B.loV+B.side) := by
        dsimp [upper,supportRadius,centerX,centerY]
        rw [abs_of_nonneg (show 0≤-W.s*B.c+W.c*B.s by dsimp [beta] at order; linarith only [order]),
          abs_of_nonneg (show 0≤-(-W.s)*B.s+W.c*B.c by dsimp [alpha] at alphaNonnegative; linarith only [alphaNonnegative])]
        dsimp [alpha,beta]
        ring
      have first := mul_le_mul_of_nonneg_left
        (show (33/20)*(B.c+B.s)+1≤B.loU+B.side by linarith only [lowerU,ha])
        (neg_nonneg.mpr order)
      have second := mul_le_mul_of_nonneg_left
        (show 1+B.c-(113/50)*B.s≤B.loV+B.side by linarith only [lowerV,ha])
        alphaNonnegative
      have delta : 0 < -beta+alpha*(1-(13/20)*B.c-(61/100)*B.s) := by
        by_cases positive : 0<alpha
        · exact add_pos_of_nonneg_of_pos (neg_nonneg.mpr order) (mul_pos positive gap)
        · have azero : alpha=0 := by linarith only [alphaNonnegative,positive]
          have negative : beta<0 := by nlinarith only [alphaUnit,azero,order]
          simpa only [azero,zero_mul,add_zero] using neg_pos.mpr negative
      have identity : -beta*((33/20)*(B.c+B.s)+1)+
          alpha*(1+B.c-(113/50)*B.s)-
          (-(33/20)*W.s+(33/20)*W.c)=
          -beta+alpha*(1-(13/20)*B.c-(61/100)*B.s) := by
        dsimp [alpha,beta]
        nlinarith only [congrArg (fun z : ℝ => W.c*z) B.unit_normal,
          congrArg (fun z : ℝ => W.s*z) B.unit_normal]
      rw [support] at sep
      linarith only [first,second,sep,sw,identity,delta]
    have positive : 0<beta := lt_of_not_ge order
    have support : upper B (-W.s) W.c=
        -beta*B.loU+alpha*(B.loV+B.side) := by
      dsimp [upper,supportRadius,centerX,centerY]
      rw [abs_of_nonpos (show -W.s*B.c+W.c*B.s≤0 by dsimp [beta] at positive; linarith only [positive]),
        abs_of_nonneg (show 0≤-(-W.s)*B.s+W.c*B.c by dsimp [alpha] at alphaNonnegative; linarith only [alphaNonnegative])]
      dsimp [alpha,beta]
      ring
    have first := mul_lt_mul_of_neg_left bottom.1 (neg_neg_of_pos positive)
    have second := mul_le_mul_of_nonneg_left
      (show 1+B.c-(113/50)*B.s≤B.loV+B.side by linarith only [lowerV,ha])
      alphaNonnegative
    let P := B.c-13/20-(13/50)*B.c*B.s-(43/500)*B.s^2
    let Q := B.s-7/20+(43/500)*B.c*B.s-(13/50)*B.s^2
    have identity : -beta*(2*B.c+(457/500)*B.s)+
        alpha*(1+B.c-(113/50)*B.s)-
        (-(33/20)*W.s+(33/20)*W.c)=W.c*P+W.s*Q := by
      dsimp [alpha,beta,P,Q]
      nlinarith only [congrArg (fun z : ℝ => W.c*z) B.unit_normal,
        congrArg (fun z : ℝ => W.s*z) B.unit_normal]
    have diagonal : 0<P+Q := by
      have h := C84PairMargins.diagonal bn steep.le
      dsimp [P,Q]
      linarith only [h]
    have parallel : 0<B.c*P+B.s*Q := by
      have identity : B.c*P+B.s*Q=1-(13/20)*B.c-(61/100)*B.s := by
        dsimp [P,Q]
        nlinarith only [B.unit_normal,congrArg (fun z : ℝ => B.s*z) B.unit_normal]
      rwa [identity]
    have cone : (B.c-B.s)*(W.c*P+W.s*Q)=
        (W.c-W.s)*(B.c*P+B.s*Q)+beta*(P+Q) := by dsimp [beta]; ring
    have firstCone := mul_nonneg (sub_nonneg.mpr wb.2) parallel.le
    have secondCone := mul_pos positive diagonal
    have margin : 0<W.c*P+W.s*Q := by
      by_contra nonpositive
      have product := mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr canonicalB) (le_of_not_gt nonpositive)
      linarith only [product,cone,firstCone,secondCone]
    rw [support] at sep
    linarith only [first,second,identity,margin,sep,sw]
  have axes := CongruentSAT.faceSeparation_of_disjoint B W same apart
  change pairRadius B W≤|B.c*(centerX W-centerX B)+B.s*(centerY W-centerY B)| ∨
    pairRadius B W≤|-B.s*(centerX W-centerX B)+B.c*(centerY W-centerY B)| ∨
    pairRadius W B≤|W.c*(centerX W-centerX B)+W.s*(centerY W-centerY B)| ∨
    pairRadius W B≤|-W.s*(centerX W-centerX B)+W.c*(centerY W-centerY B)| at axes
  have separateAxis (x y R : ℝ)
      (identity : supportRadius B x y+supportRadius W x y=R)
      (h : R≤|x*(centerX W-centerX B)+y*(centerY W-centerY B)|) :=
    separated B W x y (by rwa [identity])
  rcases axes with bu|bv|wu|wv
  · exact noBU (separateAxis _ _ _ (parallel_radius B W) bu)
  · exact noBV (separateAxis _ _ _ (transverse_radius B W) bv)
  · have identity : supportRadius B W.c W.s+supportRadius W W.c W.s=pairRadius W B := by
      rw [add_comm]; exact parallel_radius W B
    exact noWU (separateAxis _ _ _ identity wu)
  · have identity : supportRadius B (-W.s) W.c+supportRadius W (-W.s) W.c=pairRadius W B := by
      rw [add_comm]; exact transverse_radius W B
    exact noWV (separateAxis _ _ _ identity wv)

/-- All physical orientations are covered; only the two actual squares,
their genuine owned/missing points, and their disjoint interiors enter. -/
theorem impossible (B W : OpenSquare) (ha : 1<B.side) (same : B.side=W.side)
    (bottom : B.Inside 2 (457/500))
    (southeast : B.Inside (47/20) (33/20))
    (right : B.Inside (113/50) 2)
    (southwest : W.Inside (33/20) (33/20))
    (northwest : W.Inside (33/20) (47/20))
    (inner : W.Inside (87/50) 2)
    (missingSW : ¬B.Inside (33/20) (33/20))
    (missingG5 : ¬B.Inside (113/50) 1)
    (missingCorner : ¬B.Inside (12/5) 1)
    (apart : ∀ x y, ¬(B.Inside x y ∧ W.Inside x y)) : False := by
  obtain ⟨b,bc,bframe,bside,bi,_⟩ := ClosedFrames.canonical_frame B
  obtain ⟨w,wc,wframe,wside,wi,_⟩ := ClosedFrames.canonical_frame W
  have bsize : 1<b.side := by simpa only [bside] using ha
  have bb := (bi _ _).mpr bottom
  have bm := (bi _ _).mpr southeast
  have br := (bi _ _).mpr right
  have bs := C84MergedBottom.canonical_positive b bsize bc bframe bb bm br
    (fun h => missingSW ((bi _ _).mp h)) (fun h => missingCorner ((bi _ _).mp h))
  exact canonical_impossible b w bsize (by simpa only [bside,wside] using same)
    bc bs (abs_le.mp bframe).2 wc wframe bb bm br
    ((wi _ _).mpr southwest) ((wi _ _).mpr northwest) ((wi _ _).mpr inner)
    (fun h => missingSW ((bi _ _).mp h)) (fun h => missingG5 ((bi _ _).mp h))
    (fun x y h => apart x y ⟨(bi x y).mp h.1,(wi x y).mp h.2⟩)

#print axioms impossible
end N12Compact.C84MergedPair
