import Compact.Completion.OtherCases.C983.C974WallReach
import Compact.Completion.OtherCases.WallProfile.VertexGeometry

/-! C974-THREE-SQUARE-ENDING §4, in the wall-origin chart. Its input is
the actual positive wall square after the preceding lower-face theorem,
and the actual corner with its genuine two walls. -/
namespace N12Compact.Completion.OtherCases.C983.C974CornerEnding
open S12 S12Pilot FourSquareAnchors ThreeSquare ABTransverse C977ChainBridge
open C981CompletionSupportForms C1092WallProfileScalars
set_option Elab.async false

private theorem corner_lower (C : OpenSquare) (side : 1<C.side)
    (walls : ∀ x y,C.Inside x y → x≤2 ∧ -1≤y)
    (anchor : C.Inside 1 0) (missing : ¬C.Inside 1 (1/2))
    (c s : ℝ) (cn : 0≤c) (sn : 0≤s) (unit : c^2+s^2=1) :
    lower C c s≤2*c-s-C.side*profile c s := by
  let q := (pullX C).translated 2 (-1)
  have physical (x y : ℝ) : q.Inside x y ↔ C.Inside (2-x) (y-1) := by
    dsimp only [q]
    rw [inside_translated_iff,inside_pullX]
    congr 1 <;> ring
  have bound := WallProfile.corner_profile q side
    (by
      intro x y own
      have h := walls _ _ ((physical x y).mp own)
      constructor <;> linarith only [h.1,h.2])
    (by apply (physical _ _).mpr; norm_num; exact anchor)
    (by intro own; apply missing; simpa using (physical _ _).mp own) c s cn sn unit
  have cx : centerX q=2-centerX C := by
    dsimp only [q,centerX,OpenSquare.translated,pullX]
    nlinarith only [C.unit_normal]
  have cy : centerY q=1+centerY C := by
    dsimp only [q,centerY,OpenSquare.translated,pullX]
    nlinarith only [C.unit_normal]
  have radius : supportRadius q c (-s)=supportRadius C c s := by
    dsimp only [q,supportRadius,OpenSquare.translated,pullX]
    rw [show c*(-C.c)+(-s)*C.s= -(c*C.c+s*C.s) by ring,abs_neg,
      show -c*C.s+(-s)*(-C.c)= -c*C.s+s*C.c by ring]
  have support : upper q c (-s)=2*c-s-lower C c s := by
    rw [upper,cx,cy,radius,lower]
    ring
  rw [support] at bound
  change C.side*profile c s≤2*c-s-lower C c s at bound
  linarith only [bound]

private theorem profile_form (c s : ℝ) (cn : 0≤c) (unit : c^2+s^2=1) :
    profile c s=c*(2-s/(1+c))-1 := by
  have denominator : 1+c≠0 := by linarith only [cn]
  dsimp only [profile]
  field_simp [denominator]
  nlinarith only [unit]

/-- All positive quadrant directions fail; axial normals are already
excluded by the two actual strict horizontal and vertical point pairs. -/
private theorem quadrant (W C : OpenSquare) (h : C974WallReach.Data W)
    (same : W.side=C.side) (walls : ∀ x y,C.Inside x y → x≤2 ∧ -1≤y)
    (anchor : C.Inside 1 0) (missing : ¬C.Inside 1 (1/2))
    (beta c s : ℝ) (betaPositive : 0<beta) (reach : W.Inside 1 (-beta))
    (height : W.s/(1+W.c)-1/2< -beta) (small : W.s<1/2)
    (strong : W.side-W.s/2<W.loU+W.side)
    (cp : 0<c) (sp : 0<s) (unit : c^2+s^2=1) :
    lower C c s<upper W c s := by
  let z := W.s/(1+W.c)
  let w := s/(1+c)
  let alpha := c*W.c+s*W.s
  let gamma := -c*W.s+s*W.c
  have frame := C974WallReach.frame_bounds W h
  have zp : 0<z := frame.2.2.1
  have zu : z<1/3 := frame.2.2.2
  have wd := C974CornerScalars.normal_forms c s cp.le sp.le unit
  have zd := C974CornerScalars.normal_forms W.c W.s h.cosine.le h.sine.le W.unit_normal
  have wn : 0≤w := wd.1
  have wu : w≤1 := wd.2.1
  have cform : c=(1-w^2)/(1+w^2) := wd.2.2.1
  have sform : s=2*w/(1+w^2) := wd.2.2.2
  have dform : W.c=(1-z^2)/(1+z^2) := zd.2.2.1
  have tform : W.s=2*z/(1+z^2) := zd.2.2.2
  have wz : 1+w^2≠0 := by positivity
  have zz : 1+z^2≠0 := by positivity
  have wrelation : w*(1+c)=s := by dsimp only [w]; field_simp [show 1+c≠0 by linarith only [cp]]
  have pform : profile c s=c*(2-w)-1 := profile_form c s cp.le unit
  have corner := corner_lower C (by simpa only [←same] using h.sideLarge)
    walls anchor missing c s cp.le sp.le unit
  rw [←same] at corner
  by_cases low : w≤z
  · have squares := mul_nonneg (sub_nonneg.mpr low)
      (show 0≤z+w by linarith only [zp,wn])
    have identity : (1+z^2)*(1+w^2)*(c-W.c)=2*(z^2-w^2) := by
      rw [cform,dform]
      field_simp [wz,zz]
      ring
    have cd : W.c≤c := by
      apply le_of_not_gt
      intro bad
      have negative := mul_neg_of_pos_of_neg
        (show 0<(1+z^2)*(1+w^2) by positivity) (sub_neg.mpr bad)
      nlinarith only [identity,squares,negative]
    have profilePositive : 0<profile c s := by
      have product := mul_pos (show 0<c-4/5 by linarith only [cd,frame.1])
        (show 0<2-w by linarith only [low,zu])
      rw [pform]
      nlinarith only [product,low,zu]
    have strict := (strict_bounds W 1 (-beta) c s unit reach).2
    have raised := mul_pos sp (show 0< -beta-(z-1/2) by exact sub_pos.mpr height)
    have side := mul_pos (sub_pos.mpr h.sideLarge) profilePositive
    have remainder := mul_nonneg sp.le
      (show 0≤z-w+w^2/2 by nlinarith only [low,sq_nonneg w])
    have identity :
        c+s*(z-1/2)-(2*c-s-W.side*profile c s)=
          (W.side-1)*profile c s+s*(z-w+w^2/2) := by
      rw [pform,cform,sform]
      field_simp [wz]
      ring
    nlinarith only [strict,raised,side,remainder,identity,corner]
  · have order : z≤w := (lt_of_not_ge low).le
    have relative : 0≤gamma := by
      have positive := mul_nonneg (sub_nonneg.mpr order)
        (show 0≤1+w*z by positivity)
      have identity : (1+z^2)*(1+w^2)*gamma=2*(w-z)*(1+w*z) := by
        dsimp only [gamma]
        rw [cform,sform,dform,tform]
        field_simp [wz,zz]
        ring
      apply le_of_not_gt
      intro bad
      have impossible := mul_neg_of_pos_of_neg
        (show 0<(1+z^2)*(1+w^2) by positivity) bad
      nlinarith only [positive,identity,impossible]
    have ap : 0<alpha := by dsimp only [alpha]; positivity
    have o := h.origin
    simp only [OpenSquare.Inside,InBands,mul_zero,zero_mul,add_zero] at o
    have formula : upper W c s=alpha*(W.loU+W.side)+gamma*(W.loV+W.side) := by
      rw [upper_in_bands]
      change alpha*(W.loU+W.side/2)+gamma*(W.loV+W.side/2)+
        W.side/2*(|alpha|+|gamma|)=_
      rw [abs_of_nonneg ap.le,abs_of_nonneg relative]
      ring
    have first := mul_pos ap (sub_pos.mpr strong)
    have last := mul_nonneg relative o.2.2.2.le
    have full : alpha*(W.side-W.s/2)<upper W c s := by
      rw [formula]
      nlinarith only [first,last]
    by_cases moderate : 1/2≤c
    · have alphaBound : c≤alpha := by
        have first := mul_nonneg cp.le (sub_nonneg.mpr frame.2.1)
        have last := mul_nonneg h.sine.le relative
        have identity : W.c*(alpha-c)=c*(1-W.c)+W.s*gamma := by
          dsimp only [alpha,gamma]
          linear_combination c*W.unit_normal
        apply le_of_not_gt
        intro bad
        have negative := mul_neg_of_pos_of_neg h.cosine (sub_neg.mpr bad)
        linarith only [first,last,identity,negative]
      have sineUpper : s≤1 := by nlinarith only [unit,sq_nonneg c,sp]
      have wSmall : w<1 := (div_lt_one (by linarith only [cp])).mpr
        (by linarith only [sineUpper,cp])
      have profilePositive : 0<alpha+profile c s := by
        have product := mul_nonneg (sub_nonneg.mpr moderate)
          (show 0≤3-w by linarith only [wSmall])
        rw [pform]
        nlinarith only [product,alphaBound,wSmall]
      have side := mul_pos (sub_pos.mpr h.sideLarge) profilePositive
      have g := C974CornerScalars.cubic_gap W.c W.s z c s w zp zu order wu dform tform cform sform
      have identity : alpha*(W.side-W.s/2)-(2*c-s-W.side*profile c s)=
          (W.side-1)*(alpha+profile c s)+(1-W.s/2)*alpha-1+w := by
        rw [pform]
        nlinarith only [wrelation]
      change 0<(1-W.s/2)*alpha-1+w at g
      nlinarith only [full,corner,side,g,identity]
    · have steep : (3/2)*c<s := by
        nlinarith only [unit,moderate,cp,sp]
      have gain := C974CornerScalars.steep_gain W.c W.s frame.1 h.sine
        (by linarith only [small]) W.unit_normal
      have first := mul_pos h.sine (sub_pos.mpr steep)
      have positive : 0<1-W.s/2 := by linarith only [small]
      have relativeGain : c*(W.c+(3/2)*W.s)<alpha := by
        dsimp only [alpha]
        nlinarith only [first]
      have second := mul_pos positive (sub_pos.mpr relativeGain)
      have third := mul_pos cp (sub_pos.mpr gain)
      have extra := mul_pos ap (sub_pos.mpr h.sideLarge)
      have actual := (strict_bounds C 1 0 c s unit anchor).1
      nlinarith only [full,actual,second,third,extra]

/-- The actual corner contradicts the wall square after the exact
K–W lower-face comparison. No orientation assumption is made on C. -/
theorem impossible (W C : OpenSquare) (h : C974WallReach.Data W)
    (same : W.side=C.side) (walls : ∀ x y,C.Inside x y → x≤2 ∧ -1≤y)
    (anchor : C.Inside 1 0) (missing : ¬C.Inside 1 (1/2))
    (apart : ∀ x y,¬(W.Inside x y ∧ C.Inside x y)) : False := by
  obtain ⟨beta,betaPositive,reach,height,small,strong⟩ := C974WallReach.reach W h
  have noSeparator (c s : ℝ) (unit : c^2+s^2=1)
      (sep : upper W c s≤lower C c s) : False := by
    have far := (strict_bounds W (4/5) 0 c s unit h.far).2
    have actual := (strict_bounds C 1 0 c s unit anchor).1
    have below := (strict_bounds W 1 (-beta) c s unit reach).2
    have cp : 0<c := by linarith only [far,actual,sep]
    have sp : 0<s := by
      apply lt_of_not_ge
      intro bad
      have impossible := mul_nonpos_of_nonneg_of_nonpos betaPositive.le bad
      nlinarith only [below,actual,sep,impossible]
    exact (not_lt_of_ge sep)
      (quadrant W C h same walls anchor missing beta c s betaPositive reach height small strong cp sp unit)
  have axis (c s radius : ℝ) (unit : c^2+s^2=1)
      (radii : supportRadius W c s+supportRadius C c s=radius)
      (sep : radius≤|c*(centerX C-centerX W)+s*(centerY C-centerY W)|) : False := by
    rcases separated W C c s (by rwa [radii]) with forward | backward
    · exact noSeparator c s unit forward
    · apply noSeparator (-c) (-s) (by nlinarith only [unit])
      rw [WallProfile.upper_neg,WallProfile.lower_neg]
      linarith only [backward]
  have axes := CongruentSAT.faceSeparation_of_disjoint W C same apart
  change pairRadius W C≤|W.c*(centerX C-centerX W)+W.s*(centerY C-centerY W)| ∨
    pairRadius W C≤|-W.s*(centerX C-centerX W)+W.c*(centerY C-centerY W)| ∨
    pairRadius C W≤|C.c*(centerX C-centerX W)+C.s*(centerY C-centerY W)| ∨
    pairRadius C W≤|-C.s*(centerX C-centerX W)+C.c*(centerY C-centerY W)| at axes
  rcases axes with first | second | third | fourth
  · exact axis _ _ _ W.unit_normal (parallel_radius W C) first
  · exact axis _ _ _ (by nlinarith only [W.unit_normal]) (transverse_radius W C) second
  · have radii : supportRadius W C.c C.s+supportRadius C C.c C.s=pairRadius C W := by
      rw [add_comm]
      exact parallel_radius C W
    exact axis _ _ _ C.unit_normal radii third
  · have radii : supportRadius W (-C.s) C.c+supportRadius C (-C.s) C.c=pairRadius C W := by
      rw [add_comm]
      exact transverse_radius C W
    exact axis _ _ _ (by nlinarith only [C.unit_normal]) radii fourth

#print axioms impossible
end N12Compact.Completion.OtherCases.C983.C974CornerEnding
